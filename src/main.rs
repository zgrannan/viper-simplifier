mod ast_helpers;
mod queries;
mod tree_sitter_viper;
mod string_substitutions;
mod refactors;
mod replacement;
use tree_sitter::Parser;
use tree_sitter::Query;
use tree_sitter::QueryCursor;
use tree_sitter::QueryMatch;
use tree_sitter::Tree;
use tree_sitter::Node;
use string_substitutions::apply_string_substitutions;
use std::fs;
use std::borrow::Cow;
use std::env;
use std::collections::HashMap;
use queries::*;
use replacement::{Replacement, ReplacementGroup, to_replacements};
use ast_helpers::*;
use refactors::*;

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
    let mut qc = QueryCursor::new();
    for m in qc.matches(&query, tree.root_node(), source_code.as_bytes()) {
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

fn replace_decl_with_expr<'a, 'tree: 'a>(
    tree: &'tree Tree,
    decl: Node<'tree>,
    expr_text: &'a str,
    source_code: &'a str) -> ReplacementGroup<'a> {

    assert_eq!(decl.kind(), "var_decl");
    let mut replacements = Vec::new();
    let decl_ident = decl.child_by_field_name("ident").unwrap();
    let ident_text = node_text(decl_ident, source_code);
    let assignments_query = assignments_matching_ident_query(ident_text);
    let mut qc = QueryCursor::new();
    let assign_matches = qc.matches(&assignments_query, tree.root_node(), source_code.as_bytes());
    for m in assign_matches {
        let assign_stmt = get_captured_node(&assignments_query, &m, "stmt");
        replacements.push(Replacement::new(assign_stmt, Cow::Borrowed("")));
    }
    let mut ident_replacements: Vec<Replacement<'a>> = replace_all_instances_of_decl_ident_with(
        tree,
        decl_ident,
        expr_text,
        source_code,
    );
    replacements.append(&mut ident_replacements);
    ReplacementGroup::new(replacements)
}

fn remove_variables_only_assigned_to_pure<'a, 'tree: 'a>(tree: &'tree Tree, source_code: &'a str) -> Vec<ReplacementGroup<'a>> {
    let mut replacement_groups = Vec::new();
    let mut qc = QueryCursor::new();
    let decls_ts_query = get_decls_query();
    let matches = qc
        .matches(&decls_ts_query, tree.root_node(), source_code.as_bytes());
    for m in matches {
        let decl = get_captured_node(&decls_ts_query, &m, "decl");
        let decl_ident = get_captured_node(&decls_ts_query, &m, "ident");
        let ident_text = node_text(decl_ident, source_code);
        let decl_assign = decl.child_by_field_name("expr");
        if decl_assign.is_some() {
            continue // TODO: Handle this case
        }
        let assignments_query = assignments_matching_ident_query(ident_text);
        let mut qc2 = QueryCursor::new();
        let mut assign_matches = qc2.matches(&assignments_query, tree.root_node(), source_code.as_bytes());
        if let Some(assign_match) = assign_matches.next() {
            let expr = get_captured_node(&assignments_query, &assign_match, "expr");
            if is_pure(expr, source_code) && assign_matches.next().is_none() {
                let expr_text = node_text(expr, source_code);
                replacement_groups.push(
                    replace_decl_with_expr(tree, decl.child(0).unwrap(), expr_text, source_code)
                );
            }
        }
    }
    replacement_groups
}

fn force_path<'a>(tree: &'a Tree, source_code: &'a str) -> Vec<ReplacementGroup<'a>> {
    let mut replacement_groups = Vec::new();
    let to_replace = vec![("_6", "0")];
    let decls_ts_query = get_decls_query();
    let mut qc = QueryCursor::new();
    let matches = qc
        .matches(&decls_ts_query, tree.root_node(), source_code.as_bytes());
    for m in matches {
        let decl = get_captured_node(&decls_ts_query, &m, "decl");
        let decl_ident = get_captured_node(&decls_ts_query, &m, "ident");
        let ident_text = node_text(decl_ident, source_code);
        let replacement = to_replace.iter().find(|(ident, _)| ident == &ident_text);
        if let Some((_, expr_text)) = replacement {
            replacement_groups.push(replace_decl_with_expr(tree, decl.child(0).unwrap(), expr_text, source_code))
        }
    }
    replacement_groups
}

fn remove_domains<'a>(tree: &'a Tree, source_code: &'a str) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let domains = vec![
        "FloatDomain24e8"
    ];
    let query = viper_query("((domain (ident) @ident) @domain)");
    let mut qc = QueryCursor::new();
    let matches = qc
        .matches(&query, tree.root_node(), source_code.as_bytes());
    for m in matches {
        let ident = get_captured_node_text(&query, &m, "ident", source_code);
        eprintln!("Found domain {}", ident);
        if domains.iter().any(|d| d == &ident) {
            let domain = get_captured_node(&query, &m, "domain");
            replacements.push(Replacement {
                start: domain.start_byte(),
                end: domain.end_byte(),
                replacement: Cow::Borrowed("")
            });
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
        let mut replacement_groups = Vec::new();
        let mut add_replacements = |replacements| {
            for r in replacements {
                replacement_groups.push(ReplacementGroup::new(vec![r]))
            }
        };
        add_replacements(unused_label_replacements(&tree, source_str));
        add_replacements(get_simplifiable_assigns(&tree, source_str));
        add_replacements(simplify_methods(&tree, source_str));
        add_replacements(remove_unused_decls(&tree, source_str));
        add_replacements(remove_domains(&tree, source_str));

        add_replacements(get_replacements_for(&tree, SIMPLIFY_GOTO_LABEL, source_str, |query, m| {
            let goto_stmt = get_captured_node(query, &m, "goto_stmt");
            Some(Replacement {
                start: goto_stmt.start_byte(),
                end: goto_stmt.end_byte(),
                replacement: Cow::Borrowed("")
            })
        }));

        add_replacements(get_replacements_for(&tree, SIMPLIFY_IF_TRUE_QUERY, source_str, |query, m| {
            let if_stmt = get_captured_node(query, &m, "if");
            let then_clause = get_body_of_braces(if_stmt.child_by_field_name("then_clause").unwrap(), source_str);
            Some(Replacement {
                start: if_stmt.start_byte(),
                end: if_stmt.end_byte(),
                replacement: Cow::Owned(then_clause)
            })
        }));

        add_replacements(get_replacements_for(&tree, SIMPLIFY_ANDS_QUERY, source_str, |query, m| {
            let expr = get_captured_node(query, &m, "binexpr");
            let var = get_captured_node(query, &m, "lhs");
            Some(Replacement {
                start: expr.start_byte(),
                end: expr.end_byte(),
                replacement: Cow::Borrowed(var.utf8_text(source_str.as_bytes()).unwrap())
            })
        }));

        add_replacements(get_replacements_for(&tree, SIMPLIFY_IMPLICATION_QUERY, source_str, |query, m| {
            let implication = get_captured_node(query, &m, "binexpr");
            Some(Replacement {
                start: implication.start_byte(),
                end: implication.end_byte(),
                replacement: Cow::Borrowed("true")
            })
        }));

        add_replacements(get_replacements_for(&tree, SIMPLIFY_EQUALS_QUERY, source_str, |query, m| {
            let equals = get_captured_node(query, &m, "binexpr");
            Some(Replacement::new(equals, Cow::Borrowed("true")))
        }));

        add_replacements(get_replacements_for(&tree, SIMPLIFY_TERNARY_QUERY, source_str, |query, m| {
            let texpr = get_captured_node(query, &m, "ternary_expr");
            let condition = texpr.child_by_field_name("condition").unwrap();
            let then_expr = texpr.child_by_field_name("then_expr").unwrap();
            Some(Replacement {
                start: texpr.start_byte(),
                end: texpr.end_byte(),
                replacement: Cow::Owned(format!("{} && {}", node_text(condition, source_str), node_text(then_expr, source_str)))
            })
        }));

        add_replacements(get_replacements_for(&tree, SIMPLIFY_TERNARY_QUERY2, source_str, |query, m| {
            let texpr = get_captured_node(query, &m, "ternary_expr");
            let condition = texpr.child_by_field_name("condition").unwrap();
            let then_expr = texpr.child_by_field_name("then_expr").unwrap();
            Some(Replacement {
                start: texpr.start_byte(),
                end: texpr.end_byte(),
                replacement: Cow::Owned(format!("{} ==> {}", node_text(condition, source_str), node_text(then_expr, source_str)))
            })
        }));

        add_replacements(get_replacements_for(&tree, SIMPLIFY_SEQUENTIAL_IFS_QUERY, source_str, |query, m| {
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

        add_replacements(get_replacements_for(&tree, "(old_expr) @expr", source_str, |query, m| {
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

        replacement_groups.append(&mut remove_variables_only_assigned_to_pure(&tree, source_str));
        replacement_groups.append(&mut force_path(&tree, source_str));

        let replacements = to_replacements(replacement_groups);
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