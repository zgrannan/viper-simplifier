mod tree_sitter_viper;
use tree_sitter::Parser;
use tree_sitter::Query;
use tree_sitter::QueryCursor;
use tree_sitter::QueryMatch;
use tree_sitter::Tree;
use tree_sitter::Node;
use std::fs;
use std::fmt::Display;
use std::borrow::Cow;
use std::collections::VecDeque;
use std::collections::HashSet;
use std::mem::replace;


struct Replacement<'a> {
    start: usize,
    end: usize,
    replacement: Cow<'a, str>
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

fn get_captured_node<'a>(query: &'a Query, m: &'a QueryMatch<'a, 'a>, name: &str) -> Node<'a> {
    let index = query.capture_index_for_name(name).unwrap();
    // eprintln!("Index for {}: {}", name, index);
    m.captures.iter().find(|c| c.index == index).unwrap().node
}

fn main() {
    let mut source = fs::read_to_string("./test.vpr").unwrap();

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

#[derive(Clone)]
struct QueryMeta<'a> {
    capture: Option<&'a str>,
    predicate: Option<QueryPredicate<'a>>
}

impl <'a> QueryMeta<'a> {
    fn empty() -> QueryMeta<'a> {
        QueryMeta {
            capture: None,
            predicate: None
        }
    }
    const fn capture(str: &'a str) -> QueryMeta<'a> {
        QueryMeta {
            capture: Some(str),
            predicate: None
        }
    }

    fn predicate(query_predicate: QueryPredicate<'a>) -> QueryMeta {
        QueryMeta {
            capture: None,
            predicate: Some(query_predicate)
        }
    }
}

#[derive(Clone)]
struct IfQueryExpr<'a> {
    condition: Box<QueryExpr<'a>>,
    then_clause: Box<QueryExpr<'a>>,
    has_else: bool
}

#[derive(Clone)]
struct BinOpQueryExpr<'a> {
    lhs: Box<QueryExpr<'a>>,
    operator: &'a str,
    rhs: Box<QueryExpr<'a>>,
}

#[derive(Clone)]
struct SeqQueryExpr<'a> {
    fst: Box<QueryExpr<'a>>,
    snd: Box<QueryExpr<'a>>,
}

#[derive(Clone)]
enum QueryExpr<'a> {
    BinExpr(BinOpQueryExpr<'a>, QueryMeta<'a>),
    Braces(Box<Cow<'a, QueryExpr<'a>>>, QueryMeta<'a>),
    Choice(Vec<Cow<'a, QueryExpr<'a>>>),
    Comment,
    Exhale(Box<QueryExpr<'a>>, QueryMeta<'a>),
    Ident(QueryMeta<'a>),
    IfStmt(IfQueryExpr<'a>, QueryMeta<'a>),
    Inhale(Box<QueryExpr<'a>>, QueryMeta<'a>),
    Parens(Box<Cow<'a, QueryExpr<'a>>>),
    Seq(SeqQueryExpr<'a>, QueryMeta<'a>),
    Star(Box<QueryExpr<'a>>, QueryMeta<'a>),
    Wildcard,
}

#[derive(Clone)]
enum PredicateExpr<'a> {
    Capture(&'a str),
    Literal(&'a str)
}

#[derive(Clone)]
enum QueryPredicate<'a> {
    Eq(PredicateExpr<'a>, PredicateExpr<'a>)
}

impl <'a> Display for PredicateExpr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PredicateExpr::Capture(str) => write!(f, "@{}", str),
            PredicateExpr::Literal(str) => write!(f, "\"{}\"", str),
        }
    }
}

impl <'a> Display for QueryPredicate<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QueryPredicate::Eq(lhs, rhs) => write!(f, "(#eq? {} {})", lhs, rhs),
        }
    }
}

impl <'a> Display for QueryMeta<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(capture) = self.capture {
            write!(f, "@{}", capture)?
        };
        if let Some(predicate) = &self.predicate {
            write!(f, " {}", predicate)?
        };
        Ok(())
    }

}

impl <'a> Display for QueryExpr<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            QueryExpr::Braces(expr, meta) => write!(f, "(stmt {}) {}", expr, meta),
            QueryExpr::Wildcard => write!(f, "(_)"),
            QueryExpr::Comment => write!(f, "(comment)"),
            QueryExpr::Inhale(expr, meta) =>
                write!(f, "(stmt (inhale_stmt {}) {})", expr, meta),
            QueryExpr::Exhale(expr, meta) =>
                write!(f, "(stmt (exhale_stmt {}) {})", expr, meta),
            QueryExpr::Star(expr, meta) =>
                write!(f, "{}* {}", expr, meta),
            QueryExpr::Seq(seq, meta) => {
                write!(f, "({} {} {})", seq.fst, seq.snd, meta)
            }
            QueryExpr::Choice(choices) => {
                write!(f, "[")?;
                for choice in choices {
                    write!(f, "{} ", choice)?;
                }
                write!(f, "]")
            },
            QueryExpr::Parens(expr) => write!(f, "(expr {})", expr),
            QueryExpr::Ident(meta) => write!(f, "(expr (ident) {})", meta),
            QueryExpr::IfStmt(if_query, meta) => write!(f,
              "(stmt (if_stmt condition: {} then_clause: {} {}) {})",
              if_query.condition,
              if_query.then_clause,
              if (if_query.has_else) {
                ""
              } else {
                "!else_clause"
              },
              meta
            ),
            QueryExpr::BinExpr(bin_op, meta) => write!(f, "(expr
                (bin_expr lhs: {} operator: \"{}\" rhs: {}) {}
            )", bin_op.lhs, bin_op.operator, bin_op.rhs, meta),
        }
    }
}

impl <'a> QueryExpr<'a> {

    fn star(expr: QueryExpr<'a>) -> QueryExpr<'a> {
        QueryExpr::Star(Box::new(expr), QueryMeta::empty())
    }

    fn braces(expr: QueryExpr<'a>, meta: QueryMeta<'a>) -> QueryExpr<'a> {
        QueryExpr::Braces(Box::new(Cow::Owned(expr)), meta)
    }

    fn maybe_in_parens(expr: &'a QueryExpr<'a>) -> QueryExpr<'a> {
        QueryExpr::Choice(
            vec![
                Cow::Owned(QueryExpr::Parens(Box::new(Cow::Borrowed(expr)))),
                Cow::Borrowed(expr),
            ]
        )
    }

    fn if_stmt(
        condition: QueryExpr<'a>,
        then_clause: QueryExpr<'a>,
        has_else: bool,
        meta: QueryMeta<'a>
    ) -> QueryExpr<'a> {
        QueryExpr::IfStmt(IfQueryExpr {
            condition: Box::new(condition),
            then_clause: Box::new(then_clause),
            has_else
        }, meta)
    }

    fn and(lhs: QueryExpr<'a>, rhs: QueryExpr<'a>, meta: QueryMeta<'a>) -> QueryExpr<'a> {
        QueryExpr::BinExpr(BinOpQueryExpr {
            operator: "&&",
            lhs: Box::new(lhs),
            rhs: Box::new(rhs)
        }, meta)
    }

    const fn ident(capture: &'a str) -> QueryExpr<'a> {
        QueryExpr::Ident(QueryMeta::capture(capture))
    }
}

fn validate_replacements(replacements: &Vec<Replacement>) {
    replacements.iter().for_each(|r| {
        assert!(r.start < r.end);
        assert!(r.replacement.len() < r.end - r.start);
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

fn is_label_used<'a>(
    tree: &'a Tree,
    label: &'a str,
    source_code: &'a str
) -> bool {
    let mut query_cursor = QueryCursor::new();
    let query_string = format!("
        (goto_stmt target: (ident) @lbl (#eq? @lbl \"{label}\"))
        (old_expr label: (ident) @lbl (#eq? @lbl \"{label}\"))");
    let ts_query = Query::new(tree.language(), query_string.as_str()).unwrap_or_else(|err|
        panic!("Couldn't parse query {}: {}", query_string, err)
    );
    let matches = query_cursor
        .matches(&ts_query, tree.root_node(), source_code.as_bytes())
        .collect::<Vec<_>>();
    eprintln!("Label {label} has {} matches", &matches.len());
    matches.len() > 0
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

fn parse_viper_source(source_code: &str) -> Tree {
    let mut parser = Parser::new();
    let language = crate::tree_sitter_viper::viper();
    parser.set_language(language).unwrap();
    parser.parse(source_code, None).unwrap()
}