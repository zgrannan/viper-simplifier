extern "C" {
    fn tree_sitter_Viper() -> tree_sitter::Language;
}

pub fn viper() -> tree_sitter::Language {
    unsafe { tree_sitter_Viper() }
}