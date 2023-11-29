use tree_sitter::{Node, Query, QueryCursor, QueryMatch, Tree};
use crate::tree_sitter_viper;
use std::collections::HashSet;

pub fn get_captured_node_text<'a, 'b>(query: &'a Query, m: &'a QueryMatch<'a, 'a>, name: &str, source_code: &'b str) -> &'b str {
    let node = get_captured_node(query, m, name);
    node_text(node, source_code)
}

pub fn get_captured_node<'a, 'tree>(query: &'a Query, m: &'a QueryMatch<'a, 'tree>, name: &str) -> Node<'tree> {
    get_captured_nodes(query, m, name).next().expect(
        &format!(
            "Cannot find capture for {}", name)
        )
}

pub fn get_captured_nodes<'a, 'tree>(query: &'a Query, m: &'a QueryMatch<'a, 'tree>, name: &str) -> impl Iterator<Item = Node<'tree>> + 'a {
    let index = query.capture_index_for_name(name).unwrap();
    m.captures.iter().filter(move |c| c.index == index).map(move |c| c.node)
}

pub fn node_text<'a>(node: Node, source_code: &'a str) -> &'a str {
    node.utf8_text(source_code.as_bytes()).unwrap()
}

pub fn get_body_of_braces<'a> (node: Node<'a>, source_str: &'a str) -> String {
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

pub fn num_matches<'a>(
    node: Node,
    query: &'a Query,
    source_code: &'a str
) -> usize {
    let mut query_cursor = QueryCursor::new();
    query_cursor
        .matches(&query, node, source_code.as_bytes())
        .count()
}

pub fn has_matches<'a>(
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

pub fn viper_query(query: &str) -> Query {
    Query::new(tree_sitter_viper::viper(), query).unwrap_or_else(|err|
        panic!("Couldn't parse query: {}", err)
    )
}

pub fn get_labels<'a>(
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