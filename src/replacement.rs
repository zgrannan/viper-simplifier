use tree_sitter::Node;
use std::borrow::Cow;
pub struct Replacement<'a> {
    pub start: usize,
    pub end: usize,
    pub replacement: Cow<'a, str>
}

impl <'a> Replacement<'a> {
    pub fn erase(node: Node<'a>) -> Self {
        Self::new(node, Cow::Borrowed(""))
    }
    pub fn new<'tree>(node: Node<'tree>, replacement: Cow<'a, str>) -> Self {
        Replacement {
            start: node.start_byte(),
            end: node.end_byte(),
            replacement
        }
    }
}

pub struct ReplacementGroup<'a> {
    replacements: Vec<Replacement<'a>>
}

impl <'a> ReplacementGroup<'a> {
    pub fn new(mut unsorted: Vec<Replacement<'a>>) -> Self {
        sort_replacements(&mut unsorted);
        validate_replacements(&unsorted);
        ReplacementGroup {
            replacements: unsorted
        }
    }
}

pub fn validate_replacements(replacements: &Vec<Replacement>) {
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

fn sort_replacements(replacements: &mut Vec<Replacement>) {
    if replacements.len() < 2  {
        return;
    }
    replacements.sort_by(|a, b| {
        a.start.cmp(&b.start)
    });
}

fn overlaps(a: &Replacement, b: &Replacement) -> bool {
    return a.start < b.end && b.start < a.end;
}

fn can_insert(to_insert: &Replacement, replacements: &Vec<Replacement>) -> bool {
    replacements.iter().all(|r| !overlaps(to_insert, r))
}

pub fn to_replacements<'a>(groups: Vec<ReplacementGroup<'a>>) -> Vec<Replacement<'a>> {
    let mut replacements: Vec<Replacement<'a>> = Vec::new();
    for mut group in groups {
        if group.replacements.iter().all(|r| can_insert(r, &replacements)) {
            replacements.append(&mut group.replacements);
        }
    }
    sort_replacements(&mut replacements);
    validate_replacements(&replacements);
    replacements
}