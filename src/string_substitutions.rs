use regex::Regex;

fn replace_multiple_blank_lines(input: String) -> String {
    let re = Regex::new(r"\n\s*\n\s*\n+").unwrap();
    re.replace_all(&input, "\n\n").into_owned()
}

pub fn apply_string_substitutions(mut source: String) -> String {

    let string_replacements = vec![
        ("requires true\n", ""),
        ("inhale true\n", ""),
        ("Snap$struct$m_MyWrapper$0$field$f$0__$TY$__Snap$struct$m_MyWrapper$$int$", "unwrap"),
        ("cons$0$__$TY$__Snap$struct$m_MyWrapper$$int$$Snap$struct$m_MyWrapper", "mkWrapper"),
        ("f_erc20$$Erc20$$balance_of__$TY$__Snap$struct$m_erc20$$Erc20$$int$$$int$", "balance_of"),
        ("snap$__$TY$__Snap$struct$m_erc20$$Erc20$struct$m_erc20$$Erc20$Snap$struct$m_erc20$$Erc20", "Erc20"),
        ("snap$__$TY$__Snap$m_std$$result$$Result$_beg_$tuple0$$_sep_$m_erc20$$Error$_beg_$_end_$_end_$m_std$$result$$Result$_beg_$tuple0$$_sep_$m_erc20$$Error$_beg_$_end_$_end_$Snap$m_std$$result$$Result$_beg_$tuple0$$_sep_$m_erc20$$Error$_beg_$_end_$_end_", "Erc20Result"),
        ("f_erc20$$Erc20$$allowance_impl__$TY$__Snap$struct$m_erc20$$Erc20$$int$$$int$$$int$", "allowance_of"),
        ("cons$0$__$TY$__Snap$m_std$$result$$Result$_beg_$tuple0$$_sep_$m_erc20$$Error$_beg_$_end_$_end_$Snap$tuple0$$Snap$m_std$$result$$Result$_beg_$tuple0$$_sep_$m_erc20$$Error$_beg_$_end_$_end_", "mkResult"),
        ("Snap$m_std$$result$$Result$_beg_$tuple0$$_sep_$m_erc20$$Error$_beg_$_end_$_end_", "SnapResult"),
        ("f_erc20$$Erc20$$caller__$TY$__Snap$struct$m_erc20$$Erc20$$int$", "caller"),
        ("erc20$$Money", "Money")
    ];
    for (from, to) in string_replacements {
        source = source.replace(from, to);
    }
    let delete_patterns = vec![
        r"// \[mir\].*",
        r"// drop (Acc|Pred).*"
    ];

    for delete_pattern in delete_patterns {
        let regex = Regex::new(delete_pattern).unwrap();
        source = source.lines()
                    .filter(|line| !regex.is_match(line))
                    .collect::<Vec<_>>()
                    .join("\n");
    }

    replace_multiple_blank_lines(source)

}