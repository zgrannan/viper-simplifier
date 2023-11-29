pub const SIMPLIFY_ANDS_QUERY: &str =
    "(expr
        (bin_expr
            lhs: (expr (ident) @lhs)
            operator: \"&&\"
            rhs: [(expr (expr (ident) @rhs)) (expr (ident) @rhs) ]
        )
        @binexpr
        (#eq? @lhs @rhs)
    )";

pub const SIMPLIFY_IMPLICATION_QUERY: &str =
    "(expr
        (bin_expr
            lhs: (expr) @lhs
            operator: \"==>\"
        )
        @binexpr
        (#eq? @lhs \"false\")
    )";

pub const SIMPLIFY_EQUALS_QUERY: &str =
    "(expr
        (bin_expr
            lhs: (expr) @lhs
            operator: \"==\"
            rhs: (expr) @rhs
        )
        @binexpr
        (#eq? @lhs @rhs)
    )";

pub const SIMPLIFY_TERNARY_QUERY: &str =
    "(expr
        (ternary_expr
            else_expr: (expr) @else
        )
        @ternary_expr
        (#eq? @else \"false\")
    )";
pub const SIMPLIFY_TERNARY_QUERY2: &str =
"(expr
    (ternary_expr
        else_expr: (expr) @else
    )
    @ternary_expr
    (#eq? @else \"true\")
)";

pub const SIMPLIFY_IF_TRUE_QUERY: &str = "
(
    (stmt (if_stmt condition: (expr) @expr) @if)
    (#eq? @expr \"true\")
)";

pub const SIMPLIFY_SEQUENTIAL_IFS_QUERY: &str = "
    (
        (stmt (if_stmt condition: (expr (ident) @var1) then_clause: [(stmt (inhale_stmt (_)) ) (stmt (exhale_stmt (_)) ) ]*  !else_clause) @if1)
        .
        (stmt (if_stmt condition: (expr (ident) @var2) then_clause: [(stmt (inhale_stmt (_)) ) (stmt (exhale_stmt (_)) ) ]*  !else_clause) @if2)
        (#eq? @var1 @var2)
    )
";

pub const SIMPLIFY_GOTO_LABEL: &str = "
  (
    (stmt (goto_stmt target: (ident) @lbl) @goto_stmt)
    .
    (stmt (label (ident) @lbl2))
    (#eq? @lbl @lbl2)
  )
";