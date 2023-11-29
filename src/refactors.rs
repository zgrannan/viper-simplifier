use crate::ast_helpers::{has_matches, viper_query, get_labels};
use crate::replacement::Replacement;
use tree_sitter::Tree;

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

pub fn unused_label_replacements<'a>(
    tree: &'a Tree,
    source_str: &'a str
) -> Vec<Replacement<'a>> {
    let mut replacements = Vec::new();
    let labels = get_labels(&tree, source_str);
    for (node, label_text) in labels.iter() {
        if !is_label_used(&tree, label_text, source_str) {
            replacements.push(
                Replacement::erase(*node)
            );
        }
    }
    replacements
}