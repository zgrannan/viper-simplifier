extern "C" {
    fn tree_sitter_Viper() -> tree_sitter::Language;
}

pub fn viper() -> tree_sitter::Language {
    unsafe { tree_sitter_Viper() }
}

pub const NODE_TYPES: &'static str = include_str!("../../tree-sitter-viper/src/node-types.json");