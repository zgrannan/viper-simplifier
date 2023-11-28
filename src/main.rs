mod queries;
mod tree_sitter_viper;
mod string_substitutions;
use tree_sitter::Parser;
use tree_sitter::Query;
use tree_sitter::QueryCursor;
use tree_sitter::QueryMatch;
use tree_sitter::Tree;
use tree_sitter::Node;
use string_substitutions::apply_string_substitutions;
use std::fs;
use std::borrow::Cow;
use std::collections::VecDeque;
use std::collections::HashSet;
use std::env;
use std::collections::HashMap;
use std::mem::replace;
use queries::*;

struct Replacement<'a> {
    start: usize,
    end: usize,
    replacement: Cow<'a, str>
}

fn get_body_of_braces<'a> (node: Node<'a>, source_str: &'a str) -> String {
    let mut buf = String::new();
    let mut node = node;
    while node.next_named_sibling().is_some() {
        node = node.next_named_sibling().unwrap();
        buf.push_str(node.utf8_text(source_str.as_bytes()).unwrap());
        if node.next_named_sibling().is_some() {
            buf.push_str("\n");
        }
    }
    return buf
}

fn get_captured_node_text<'a, 'b>(query: &'a Query, m: &'a QueryMatch<'a, 'a>, name: &str, source_code: &'b str) -> &'b str {
    let node = get_captured_node(query, m, name);
    node_text(node, source_code)
}

fn get_captured_node<'a, 'tree>(query: &'a Query, m: &'a QueryMatch<'a, 'tree>, name: &str) -> Node<'tree> {
    get_captured_nodes(query, m, name).next().expect(
        &format!(
            "Cannot find capture for {}", name)
        )
}

fn get_captured_nodes<'a, 'tree>(query: &'a Query, m: &'a QueryMatch<'a, 'tree>, name: &str) -> impl Iterator<Item = Node<'tree>> + 'a {
    let index = query.capture_index_for_name(name).unwrap();
    m.captures.iter().filter(move |c| c.index == index).map(move |c| c.node)
}

fn node_text<'a>(node: Node, source_code: &'a str) -> &'a str {
    node.utf8_text(source_code.as_bytes()).unwrap()
}

fn is_side_effect_free<'a>(node: Node<'a>, source_code: &'a str) -> bool {
    if is_constant(node, source_code)  {
        true
    } else {
        let text = node_text(node, source_code);
        text == "builtin$havoc_ref()" || text == "builtin$havoc_int()"
    }
}

fn is_pure<'a>(node: Node<'a>, source_code: &'a str) -> bool {
    is_constant(node, source_code)
        || node.child(0).unwrap().kind() == "ident"
}

fn is_constant<'a>(node: Node<'a>, source_code: &'a str) -> bool {
    let text = node_text(node, source_code);
    text == "true" || text == "false"
}

fn assignments_matching_ident_query(ident: &str) -> Query {
    viper_query(
        &format!(
            "((assign_stmt target: (_) @ident expr: (_) @expr) @stmt
             (#eq? @ident \"{ident}\"))"
        )
    )
}

fn matching_ident_query(ident: &str) -> Query {
    viper_query(&format!("((ident) @ident (#eq? @ident \"{}\"))", ident))
}

fn expr_matching_ident_query(ident: &str) -> Query {
    viper_query(&format!("(expr (ident) @ident (#eq? @ident \"{}\"))", ident))
}

fn viper_query(query: &str) -> Query {
    Query::new(tree_sitter_viper::viper(), query).unwrap_or_else(|err|
        panic!("Couldn't parse query: {}", err)
    )
}


fn constant_replacements<'a>(node: Node<'a>, dict: &HashMap<&'a str, &'a str>, source_code: &'a str) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    for (ident, rep) in dict.iter() {
        let query = matching_ident_query(ident);
        let mut qc = QueryCursor::new();
        for m in qc.matches(&query, node, source_code.as_bytes()) {
            let ident_node = get_captured_node(&query, &m, "ident");
            let rep = Replacement {
                start: ident_node.start_byte(),
                end: ident_node.end_byte(),
                replacement: Cow::Borrowed(rep)
            };
            replacements.push(rep);
        }
    }
    replacements
}

fn replace_all_instances_of_decl_ident_with<'a>(
    tree: &'a Tree,
    decl_ident: Node<'a>,
    replacement: &'a str,
    source_code: &'a str
) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let ident_text = node_text(decl_ident, source_code);
    let query = expr_matching_ident_query(ident_text);
    eprintln!("Lookup {ident_text}");
    let mut qc = QueryCursor::new();
    for m in qc.matches(&query, tree.root_node(), source_code.as_bytes()) {
        eprintln!("MATCH");
        let ident_node = get_captured_node(&query, &m, "ident");
        let rep = Replacement {
            start: ident_node.start_byte(),
            end: ident_node.end_byte(),
            replacement: Cow::Borrowed(replacement)
        };
        replacements.push(rep);
    }
    replacements
}

fn constant_propagation<'a>(method: Node<'a>, source_code: &'a str) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let body = method.child_by_field_name("body");
    if body.is_none() {
        return replacements
    }
    let mut curr_stmt_option = body.unwrap().named_child(0);
    let mut dict: HashMap<&'a str, &'a str> = HashMap::new();
    while curr_stmt_option.is_some() {
        let curr_stmt = curr_stmt_option.unwrap();
        curr_stmt_option = curr_stmt.next_named_sibling();
        if curr_stmt.kind() == "comment" {
            continue;
        }
        if curr_stmt.child(0).unwrap().kind() == "var_decl" {
            let decl = curr_stmt.child(0).unwrap();
            let ident = decl.child_by_field_name("ident").unwrap();
            let expr_option = decl.child_by_field_name("expr");
            if let Some(expr) = expr_option {
                replacements.append(&mut constant_replacements(expr, &dict, source_code));
                if is_constant(expr, source_code) {
                    dict.insert(node_text(ident, source_code), node_text(expr, source_code));
                }
            };
        } else if curr_stmt.child(0).unwrap().kind() == "assign_stmt" {
            let assign = curr_stmt.child(0).unwrap();
            let expr = assign.child_by_field_name("expr").unwrap();
            replacements.append(&mut constant_replacements(expr, &dict, source_code));
            if assign.child_by_field_name("target").unwrap().child(0).unwrap().kind() == "ident" {
                let ident_text = node_text(assign.child_by_field_name("target").unwrap(), source_code);
                if is_constant(expr, source_code) {
                    dict.insert(ident_text, node_text(expr, source_code));
                } else {
                    dict.remove(ident_text);
                }
            }
        } else {
            replacements.append(&mut constant_replacements(curr_stmt, &dict, source_code));
        }
    }
    return replacements;
}

fn get_decls_query() -> Query {
    viper_query("(stmt (var_decl (ident) @ident (typ) @typ)) @decl")
}

fn remove_variables_only_assigned_to_pure<'a, 'tree: 'a>(tree: &'tree Tree, source_code: &'a str) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let mut qc = QueryCursor::new();
    let decls_ts_query = get_decls_query();
    let matches = qc
        .matches(&decls_ts_query, tree.root_node(), source_code.as_bytes());
    for m in matches {
        let decl = get_captured_node(&decls_ts_query, &m, "decl");
        let decl_ident = get_captured_node(&decls_ts_query, &m, "ident");
        let ident_text = node_text(decl_ident, source_code);
        eprintln!("Check {ident_text}");
        let decl_assign = decl.child_by_field_name("expr");
        if decl_assign.is_some() {
            continue // TODO: Handle this case
        }
        let assignments_query = assignments_matching_ident_query(ident_text);
        let mut qc2 = QueryCursor::new();
        let mut assign_matches = qc2.matches(&assignments_query, tree.root_node(), source_code.as_bytes());
        if let Some(assign_match) = assign_matches.next() {
            eprintln!("{ident_text} has assign");
            let expr = get_captured_node(&assignments_query, &assign_match, "expr");
            let assign_stmt = get_captured_node(&assignments_query, &assign_match, "stmt");
            if is_pure(expr, source_code) && assign_matches.next().is_none() {
                eprintln!("{ident_text} will be eliminated");
                replacements.push(Replacement {
                    start: decl.start_byte(),
                    end: decl.end_byte(),
                    replacement: Cow::Borrowed("")
                });
                replacements.push(Replacement {
                    start: assign_stmt.start_byte(),
                    end: assign_stmt.end_byte(),
                    replacement: Cow::Borrowed("")
                });
                let mut ident_replacements: Vec<Replacement<'a>> = replace_all_instances_of_decl_ident_with(
                    tree,
                    decl_ident,
                    node_text(expr, source_code),
                    source_code,
                );
                replacements.append(&mut ident_replacements);
            }

        }
    }
    replacements
}

fn get_simplifiable_assigns<'a>(tree: &'a Tree, source_code: &'a str) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let mut qc = QueryCursor::new();
    let decls_ts_query = get_decls_query();
    let matches = qc
        .matches(&decls_ts_query, tree.root_node(), source_code.as_bytes());
    for m in matches {
        let decl = get_captured_node(&decls_ts_query, &m, "decl");
        let ident_text = get_captured_node_text(&decls_ts_query, &m, "ident", source_code);
        let typ_text = get_captured_node_text(&decls_ts_query, &m, "typ", source_code);
        let mut next_sibling_option = decl.next_sibling();
        let ident_query = matching_ident_query(ident_text);
        while next_sibling_option.is_some() {
            let next_sibling = next_sibling_option.unwrap();
            if has_matches(next_sibling, &ident_query, source_code) {
                if next_sibling.child(0).unwrap().kind() == "assign_stmt" {
                    let assign_stmt = next_sibling.child(0).unwrap();
                    let target = assign_stmt.child_by_field_name("target").unwrap();
                    let expr = assign_stmt.child_by_field_name("expr").unwrap();
                    let expr_text = node_text(expr, source_code);
                    if !is_side_effect_free(expr, source_code) {
                        break;
                    }
                    if node_text(target, source_code) == ident_text && !has_matches(expr, &ident_query, source_code) {
                        let rep1 = Replacement {
                            start: decl.start_byte(),
                            end: decl.end_byte(),
                            replacement: Cow::Owned(format!("var {ident_text}: {typ_text} := {expr_text}"))
                        };
                        let rep2 = Replacement {
                            start: assign_stmt.start_byte(),
                            end: assign_stmt.end_byte(),
                            replacement: Cow::Borrowed("")
                        };
                        replacements.push(rep1);
                        replacements.push(rep2);
                    }
                }
                break;
            }
            next_sibling_option = next_sibling.next_sibling();
        }
    }
    return replacements
}


fn unused_label_replacements<'a>(
    tree: &'a Tree,
    source_str: &'a str
) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let labels = get_labels(&tree, source_str);
    for (node, label_text) in labels.iter() {
        if !is_label_used(&tree, label_text, source_str) {
            replacements.push(
                Replacement {
                    start: node.start_byte(),
                    end: node.end_byte(),
                    replacement: Cow::Borrowed("")
                }
            );
        }
    }
    replacements
}

fn simplify_methods<'a>(
    tree: &'a Tree,
    source_str: &'a str
) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let methods_query = viper_query("(method) @method");
    let mut qc = QueryCursor::new();
    qc.matches(&methods_query, tree.root_node(), source_str.as_bytes()).for_each(|m| {
        let method = m.captures.iter().find(|c| c.index == 0).unwrap().node;
        replacements.append(&mut constant_propagation(method, source_str));
    });
    replacements
}

fn remove_unused_decls<'a>(
    tree: &'a Tree,
    source_str: &'a str
) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let decls_query = viper_query("(var_decl ident: (_) @ident) @decl");
    let mut qc = QueryCursor::new();
    qc.matches(&decls_query, tree.root_node(), source_str.as_bytes()).for_each(|m| {
        let ident_text = get_captured_node_text(&decls_query, &m, "ident", source_str);
        let decl = get_captured_node(&decls_query, &m, "decl");
        if num_matches(tree.root_node(), &matching_ident_query(ident_text), source_str) == 1 {
            replacements.push(Replacement {
                start: decl.start_byte(),
                end: decl.end_byte(),
                replacement: Cow::Borrowed("")
            });
        }
    });
    replacements
}

fn main() {

    let filename = env::args().nth(1).unwrap();
    let mut source = fs::read_to_string(filename).unwrap();
    let mut i = 0;
    loop {
        source = apply_string_substitutions(source);
        let mut buffer = String::new();
        let source_str = source.as_str();
        let tree = parse_viper_source(source_str);
        let mut replacements = Vec::new();
        replacements.append(&mut unused_label_replacements(&tree, source_str));
        replacements.append(&mut get_simplifiable_assigns(&tree, source_str));
        replacements.append(&mut simplify_methods(&tree, source_str));
        replacements.append(&mut remove_unused_decls(&tree, source_str));



        replacements.append(&mut get_replacements_for(&tree, SIMPLIFY_GOTO_LABEL, source_str, |query, m| {
            let goto_stmt = get_captured_node(query, &m, "goto_stmt");
            Some(Replacement {
                start: goto_stmt.start_byte(),
                end: goto_stmt.end_byte(),
                replacement: Cow::Borrowed("")
            })
        }));

        replacements.append(&mut get_replacements_for(&tree, SIMPLIFY_IF_TRUE_QUERY, source_str, |query, m| {
            let if_stmt = get_captured_node(query, &m, "if");
            let then_clause = node_text(if_stmt.child_by_field_name("then_clause").unwrap(), source_str);
            eprintln!("Then clause: {}", then_clause);
            Some(Replacement {
                start: if_stmt.start_byte(),
                end: if_stmt.end_byte(),
                replacement: Cow::Borrowed(then_clause)
            })
        }));

        replacements.append(&mut get_replacements_for(&tree, SIMPLIFY_ANDS_QUERY, source_str, |query, m| {
            let expr = get_captured_node(query, &m, "binexpr");
            let var = get_captured_node(query, &m, "lhs");
            Some(Replacement {
                start: expr.start_byte(),
                end: expr.end_byte(),
                replacement: Cow::Borrowed(var.utf8_text(source_str.as_bytes()).unwrap())
            })
        }));

        replacements.append(&mut get_replacements_for(&tree, SIMPLIFY_IMPLICATION_QUERY, source_str, |query, m| {
            let implication = get_captured_node(query, &m, "binexpr");
            Some(Replacement {
                start: implication.start_byte(),
                end: implication.end_byte(),
                replacement: Cow::Borrowed("true")
            })
        }));

        replacements.append(&mut get_replacements_for(&tree, SIMPLIFY_TERNARY_QUERY, source_str, |query, m| {
            let texpr = get_captured_node(query, &m, "ternary_expr");
            let condition = texpr.child_by_field_name("condition").unwrap();
            let then_expr = texpr.child_by_field_name("then_expr").unwrap();
            Some(Replacement {
                start: texpr.start_byte(),
                end: texpr.end_byte(),
                replacement: Cow::Owned(format!("{} && {}", node_text(condition, source_str), node_text(then_expr, source_str)))
            })
        }));

        replacements.append(&mut get_replacements_for(&tree, SIMPLIFY_TERNARY_QUERY2, source_str, |query, m| {
            let texpr = get_captured_node(query, &m, "ternary_expr");
            let condition = texpr.child_by_field_name("condition").unwrap();
            let then_expr = texpr.child_by_field_name("then_expr").unwrap();
            Some(Replacement {
                start: texpr.start_byte(),
                end: texpr.end_byte(),
                replacement: Cow::Owned(format!("{} ==> {}", node_text(condition, source_str), node_text(then_expr, source_str)))
            })
        }));

        replacements.append(&mut get_replacements_for(&tree, SIMPLIFY_SEQUENTIAL_IFS_QUERY, source_str, |query, m| {
            let condition_node = get_captured_node(query, &m, "var1");
            let condition = condition_node.utf8_text(source_str.as_bytes()).unwrap();
            let second_condition = get_captured_node(query, &m, "var2").utf8_text(source_str.as_bytes()).unwrap();
            assert_eq!(condition, second_condition, "Error, around {}", condition_node.start_position());
            let first_if = m.captures[0].node;
            let second_if = m.captures[2].node;
            let b0 = first_if.child_by_field_name("then_clause").unwrap();
            let b1 = second_if.child_by_field_name("then_clause").unwrap();
            let replacement = format!(
                "if({condition}){{\n\
                    {}\n\
                    {}\n\
                }}",
                get_body_of_braces(b0, source_str),
                get_body_of_braces(b1, source_str)
            );
            Some(Replacement {
                start: first_if.start_byte(),
                end: second_if.end_byte(),
                replacement: Cow::Owned(replacement),
            })
        }));

        replacements.append(&mut get_replacements_for(&tree, "(old_expr) @expr", source_str, |query, m| {
            let old_expr = get_captured_node(query, &m, "expr");
            let inner = old_expr.child_by_field_name("expr").unwrap();
            if inner.child(0).unwrap().kind() == "ident" {
                Some(Replacement {
                    start: old_expr.start_byte(),
                    end: old_expr.end_byte(),
                    replacement: Cow::Borrowed(node_text(inner, source_str))
                })
            } else {
                None
            }
        }));

        replacements.append(&mut remove_variables_only_assigned_to_pure(&tree, source_str));

        sort_replacements(&mut replacements);
        let replacements = remove_overlapping_replacements(replacements);
        validate_replacements(&replacements);
        let mut last_byte = 0;
        eprintln!("Iteration {i} (code size: {}): Made {} replacements", source_str.len(), replacements.len());
        for node in replacements {
            eprintln!("Replacing {} with {}", &source_str[node.start..node.end], node.replacement);
            buffer.push_str(&source_str[last_byte..node.start]);
            buffer.push_str(node.replacement.as_ref());
            last_byte = node.end;
        }
        buffer.push_str(&source[last_byte..]);
        if source == buffer {
            break;
        } else {
            source = buffer.clone();
        }
        i += 1
    }
    println!("{}", source);
}


fn validate_replacements(replacements: &Vec<Replacement>) {
    replacements.iter().for_each(|r| {
        assert!(r.start <= r.end);
    });
    if replacements.len() >= 2 {
        let mut i = 0;
        while i < replacements.len() - 1 {
            assert!(replacements[i].end <= replacements[i + 1].start);
            i += 1;
        }
    };
}

fn remove_overlapping_replacements(mut input: Vec<Replacement>) -> Vec<Replacement> {
    if input.len() < 2  {
        return input
    }
    let mut deque = VecDeque::new();
    let last = input.pop().unwrap();
    deque.push_back(last);
    while !input.is_empty() {
        let last = input.pop().unwrap();
        if last.end <= deque.front().unwrap().start {
            deque.push_front(last);
        }
    }
    deque.into()
}

fn sort_replacements(replacements: &mut Vec<Replacement>) {
    if replacements.len() < 2  {
        return;
    }
    replacements.sort_by(|a, b| {
        a.start.cmp(&b.start)
    });
}

fn get_labels<'a>(
    tree: &'a Tree,
    source_code: &'a str
) -> HashSet<(Node<'a>, &'a str)> {
    let mut query_cursor = QueryCursor::new();
    let query_string = "(stmt (label (_) @ident))";
    let ts_query = Query::new(tree.language(), query_string).unwrap_or_else(|err|
        panic!("Couldn't parse query: {}", err)
    );
    let matches = query_cursor.matches(&ts_query, tree.root_node(), source_code.as_bytes());
    matches.map(|m| {
        let ident_node = m.captures.iter().find(|c| c.index == 0).unwrap().node;
        let label_text = ident_node.utf8_text(source_code.as_bytes()).unwrap();
        (ident_node.parent().unwrap(), label_text)
    }).collect()
}

fn has_matches<'a>(
    node: Node,
    query: &'a Query,
    source_code: &'a str
) -> bool {
    let mut query_cursor = QueryCursor::new();
    query_cursor
        .matches(&query, node, source_code.as_bytes())
        .next()
        .is_some()
}

fn num_matches<'a>(
    node: Node,
    query: &'a Query,
    source_code: &'a str
) -> usize {
    let mut query_cursor = QueryCursor::new();
    query_cursor
        .matches(&query, node, source_code.as_bytes())
        .count()
}

fn is_label_used<'a>(
    tree: &'a Tree,
    label: &'a str,
    source_code: &'a str
) -> bool {
    let query_string = viper_query(&format!("
        (goto_stmt target: (ident) @lbl (#eq? @lbl \"{label}\"))
        (old_expr label: (ident) @lbl (#eq? @lbl \"{label}\"))"));
    has_matches(tree.root_node(), &query_string, source_code)
}

fn get_replacements_for<'a, 'b: 'a, F>(
    tree: &'a Tree,
    query: &'a str,
    source_code: &'a str,
    f: F
) ->  Vec<Replacement<'a>>
  where F: Fn(&Query, QueryMatch)  -> Option<Replacement<'a>>
{
    let query = viper_query(query);
    let mut query_cursor = QueryCursor::new();
    let matches = query_cursor.matches(&query, tree.root_node(), source_code.as_bytes());
    matches.map(|m| {
        f(&query, m)
    }).filter(|r| r.is_some()).map(|r| r.unwrap()).collect()
}

fn parse_viper_source(source_code: &str) -> Tree {
    let mut parser = Parser::new();
    let language = crate::tree_sitter_viper::viper();
    parser.set_language(language).unwrap();
    parser.parse(source_code, None).unwrap()
}