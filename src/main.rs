mod tree_sitter_viper;
mod query_expr;
use query_expr::*;
use tree_sitter::Parser;
use tree_sitter::Query;
use tree_sitter::QueryCursor;
use tree_sitter::QueryMatch;
use tree_sitter::Tree;
use tree_sitter::Node;
use std::fs;
use std::borrow::Cow;
use std::collections::VecDeque;
use std::collections::HashSet;
use std::env;
use std::os::unix::ffi::OsStrExt;


struct Replacement<'a> {
    start: usize,
    end: usize,
    replacement: Cow<'a, str>
}

impl <'a> Replacement<'a> {
    fn new(start: usize, end: usize, replacement: Cow<'a, str>) -> Replacement<'a> {
        assert!(start <= end);
        Replacement {
            start,
            end,
            replacement
        }
    }
}

fn get_body_of_braces<'a> (node: Node<'a>, source_str: &'a str) -> String {
    let mut buf = String::new();
    let mut node = node;
    while(node.next_named_sibling().is_some()) {
        node = node.next_named_sibling().unwrap();
        buf.push_str(node.utf8_text(source_str.as_bytes()).unwrap());
        if(node.next_named_sibling().is_some()){
            buf.push_str("\n");
        }
    }
    return buf
}

fn get_captured_node_text<'a>(query: &'a Query, m: &'a QueryMatch<'a, 'a>, name: &str, source_code: &'a str) -> &'a str {
    let node = get_captured_node(query, m, name);
    node_text(node, source_code)
}

fn get_captured_node<'a>(query: &'a Query, m: &'a QueryMatch<'a, 'a>, name: &str) -> Node<'a> {
    get_captured_nodes(query, m, name)[0]
}

fn get_captured_node_with_text<'a>(query: &'a Query, m: &'a QueryMatch, name: &str, source_code: &'a str) -> (Node<'a>, &'a str) {
    let node = get_captured_node(query, m, name);
    (node, node_text(node, source_code))
}

fn get_captured_nodes<'a>(query: &'a Query, m: &'a QueryMatch<'a, 'a>, name: &str) -> Vec<Node<'a>> {
    let index = query.capture_index_for_name(name).unwrap();
    m.captures.iter().filter(|c| c.index == index).map(|c| c.node).collect::<Vec<_>>()
}

fn node_text<'a>(node: Node, source_code: &'a str) -> &'a str {
    node.utf8_text(source_code.as_bytes()).unwrap()
}

fn is_constant<'a>(node: Node<'a>, source_code: &'a str) -> bool {
    let text = node_text(node, source_code);
    text == "true" || text == "false"
}

fn get_simplifiable_assigns<'a>(tree: &'a Tree, source_code: &'a str) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let mut qc = QueryCursor::new();
    let decls_query = "(stmt (var_decl (ident) @ident (typ) @typ)) @decl";
    let decls_ts_query = Query::new(tree.language(), decls_query).unwrap_or_else(|err|
        panic!("Couldn't parse query: {}", err)
    );
    let matches = qc
        .matches(&decls_ts_query, tree.root_node(), source_code.as_bytes());
    for m in matches {
        let decl = get_captured_node(&decls_ts_query, &m, "decl");
        let ident_text = get_captured_node_text(&decls_ts_query, &m, "ident", source_code);
        let typ_text = get_captured_node_text(&decls_ts_query, &m, "typ", source_code);
        let mut next_sibling_option = decl.next_sibling();
        let matching_ident_query = format!("((ident) @ident (#eq? @ident \"{}\"))", ident_text);
        while next_sibling_option.is_some() {
            let next_sibling = next_sibling_option.unwrap();
            if has_matches(next_sibling, &matching_ident_query, source_code) {
                if next_sibling.child(0).unwrap().kind() == "assign_stmt" {
                    let assign_stmt = next_sibling.child(0).unwrap();
                    let target = assign_stmt.child_by_field_name("target").unwrap();
                    let expr = assign_stmt.child_by_field_name("expr").unwrap();
                    if !is_constant(expr, source_code) {
                        break;
                    }
                    let expr_text = node_text(expr, source_code);
                    if node_text(target, source_code) == ident_text && !has_matches(expr, &matching_ident_query, source_code) {
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

fn run_query(source: &str, query: &str) {
    let tree = parse_rust_source(source);
    let mut qc = QueryCursor::new();
    let ts_query = Query::new(tree.language(), query).unwrap_or_else(|err|
        panic!("Couldn't parse query: {}", err)
    );
    let matches = qc
        .matches(&ts_query, tree.root_node(), source.as_bytes())
        .collect::<Vec<_>>();
    assert!(ts_query.pattern_count() == 1, "Expected one pattern");
    for m in matches.iter() {
        assert!(m.pattern_index == 0, "Expected pattern index to be 0");
        eprintln!("----");
        for capture in m.captures.iter() {
            eprintln!("Capture {} for {}",
                capture.node.utf8_text(source.as_bytes()).unwrap(),
                ts_query.capture_names()[capture.index as usize]
            );
        }
    }
}

fn main() {

    // let source = "fn main() {
    //     let a = 1;
    //     let b = 2;
    //     let c = 3;
    // }";

    // let query = "(
    //     (let_declaration)* @bar
    //     (let_declaration) @baz
    // )";

    // run_query(source, query);
    // return;

    // let tree = parse_viper_source(source);
    // println!("{}", tree.root_node().to_sexp());
    // return;
    let filename = env::args().nth(1).unwrap();
    let mut source = fs::read_to_string(filename).unwrap();
    // let tree = parse_viper_source(&source);
    // get_simplifiable_assigns(&tree, &source);
    // return;

    // let mut source = fs::read_to_string("../tree-sitter-viper/test.vpr").unwrap();
    let mut i = 0;
    loop {
        let mut buffer = String::new();
        let source_str = source.as_str();
        let tree = parse_viper_source(source_str);
        let labels = get_labels(&tree, source_str);
        eprintln!("Labels: {:?}", labels);
        let mut replacements = Vec::new();
        for (node, label_text) in labels.iter() {
            if !is_label_used(&tree, label_text, source_str) {
                eprintln!("Unused label {}", label_text);
                replacements.push(
                    Replacement {
                        start: node.start_byte(),
                        end: node.end_byte(),
                        replacement: Cow::Borrowed("")
                    }
                );
            }
        }
        replacements.append(&mut get_simplifiable_assigns(&tree, source_str));

        replacements.append(&mut get_replacements_for(&tree, simplify_and(), source_str, |query, m| {
            let if_clause = get_captured_node(query, &m, "binexpr");
            let var = get_captured_node(query, &m, "lhs");
            Some(Replacement {
                start: if_clause.start_byte(),
                end: if_clause.end_byte(),
                replacement: Cow::Borrowed(var.utf8_text(source_str.as_bytes()).unwrap())
            })
        }));

        replacements.append(&mut get_replacements_for(&tree, simplify_ifs(), source_str, |query, m| {
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

        sort_replacements(&mut replacements);
        let replacements = remove_overlapping_replacements(replacements);
        validate_replacements(&replacements);
        let mut last_byte = 0;
        if replacements.len() == 0 {
            break;
        } else {
            eprintln!("Iteration {i} (code size: {}): Made {} replacements", source_str.len(), replacements.len());
        }
        for node in replacements {
            // eprintln!("Replacing {} with {}", &source_str[node.start..node.end], node.replacement);
            buffer.push_str(&source_str[last_byte..node.start]);
            buffer.push_str(node.replacement.as_ref());
            last_byte = node.end;
        }
        buffer.push_str(&source[last_byte..]);
        source = buffer.clone();
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
    query: &'a str,
    source_code: &'a str
) -> bool {
    let mut query_cursor = QueryCursor::new();
    let ts_query = Query::new(node.language(), query).unwrap_or_else(|err|
        panic!("Couldn't parse query {}: {}", query, err)
    );
    let matches = query_cursor
        .matches(&ts_query, node, source_code.as_bytes())
        .collect::<Vec<_>>();
    matches.len() > 0
}

fn is_label_used<'a>(
    tree: &'a Tree,
    label: &'a str,
    source_code: &'a str
) -> bool {
    let query_string = format!("
        (goto_stmt target: (ident) @lbl (#eq? @lbl \"{label}\"))
        (old_expr label: (ident) @lbl (#eq? @lbl \"{label}\"))");
    has_matches(tree.root_node(), &query_string, source_code)
}

fn get_replacements_for<'a, 'b: 'a, F>(
    tree: &'a Tree,
    query: QueryExpr<'b>,
    source_code: &'a str,
    f: F
) ->  Vec<Replacement<'a>>
  where F: Fn(&Query, QueryMatch)  -> Option<Replacement<'a>>
{
    let query_string = format!("{}", query);
    // eprintln!("Query string: {}", query_string);
    let ts_query = Query::new(tree.language(), query_string.as_str()).unwrap_or_else(|err|
        panic!("Couldn't parse query: {}", err)
    );
    // eprintln!("Query Captures: {}", ts_query.capture_names().join(", "));
    let mut query_cursor = QueryCursor::new();
    let matches = query_cursor.matches(&ts_query, tree.root_node(), source_code.as_bytes());
    matches.map(|m| {
        f(&ts_query, m)
    }).filter(|r| r.is_some()).map(|r| r.unwrap()).collect()
}

const RHS_IDENT: &'static QueryExpr<'static> = &QueryExpr::ident("rhs");

fn simplify_ifs() -> QueryExpr<'static> {
    let side_effect_free_body =
        QueryExpr::star(
            QueryExpr::Choice(
                vec![
                    Cow::Owned(QueryExpr::Inhale(
                        Box::new(QueryExpr::Wildcard),
                        QueryMeta::empty()
                    )),
                    Cow::Owned(QueryExpr::Exhale(
                        Box::new(QueryExpr::Wildcard),
                        QueryMeta::empty()
                    )),
                ]
            ),
        );
    QueryExpr::Seq(
        SeqQueryExpr {
            fst: Box::new(QueryExpr::if_stmt(
                QueryExpr::ident("var1"),
                side_effect_free_body.clone(),
                false,
                QueryMeta { capture: Some("if1"), predicate: None }
            )),
            snd: Box::new(QueryExpr::if_stmt(
                QueryExpr::ident("var2"),
                side_effect_free_body,
                false,
                QueryMeta { capture: Some("if2"), predicate: None }
            )),
        },
        QueryMeta {
            capture: None,
            predicate: Some(QueryPredicate::Eq(
                PredicateExpr::Capture("var1"),
                PredicateExpr::Capture("var2")
            ))
        }
    )
}

fn simplify_and() -> QueryExpr<'static> {
    QueryExpr::and(
        QueryExpr::ident("lhs"),
        QueryExpr::maybe_in_parens(
            RHS_IDENT
        ),
        QueryMeta {
            capture: Some("binexpr"),
            predicate: Some(QueryPredicate::Eq(
                PredicateExpr::Capture("lhs"),
                PredicateExpr::Capture("rhs")
            ))
        }
    )
}

fn parse_rust_source(source_code: &str) -> Tree {
    let mut parser = Parser::new();
    let language = tree_sitter_rust::language();
    parser.set_language(language).unwrap();
    parser.parse(source_code, None).unwrap()
}

fn parse_viper_source(source_code: &str) -> Tree {
    let mut parser = Parser::new();
    let language = crate::tree_sitter_viper::viper();
    parser.set_language(language).unwrap();
    parser.parse(source_code, None).unwrap()
}