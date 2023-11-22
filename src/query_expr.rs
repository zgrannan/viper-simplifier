use std::fmt::Display;
use std::borrow::Cow;

#[derive(Clone)]
pub struct QueryMeta<'a> {
    pub capture: Option<&'a str>,
    pub predicate: Option<QueryPredicate<'a>>
}

impl <'a> QueryMeta<'a> {
    pub fn empty() -> QueryMeta<'a> {
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
pub struct IfQueryExpr<'a> {
    condition: Box<QueryExpr<'a>>,
    then_clause: Box<QueryExpr<'a>>,
    has_else: bool
}

#[derive(Clone)]
pub struct BinOpQueryExpr<'a> {
    lhs: Box<QueryExpr<'a>>,
    operator: &'a str,
    rhs: Box<QueryExpr<'a>>,
}

#[derive(Clone)]
pub struct SeqQueryExpr<'a> {
    pub fst: Box<QueryExpr<'a>>,
    pub snd: Box<QueryExpr<'a>>,
}

#[derive(Clone)]
pub enum QueryExpr<'a> {
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
pub enum PredicateExpr<'a> {
    Capture(&'a str),
    Literal(&'a str)
}

#[derive(Clone)]
pub enum QueryPredicate<'a> {
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

    pub fn star(expr: QueryExpr<'a>) -> QueryExpr<'a> {
        QueryExpr::Star(Box::new(expr), QueryMeta::empty())
    }

    fn braces(expr: QueryExpr<'a>, meta: QueryMeta<'a>) -> QueryExpr<'a> {
        QueryExpr::Braces(Box::new(Cow::Owned(expr)), meta)
    }

    pub fn maybe_in_parens(expr: &'a QueryExpr<'a>) -> QueryExpr<'a> {
        QueryExpr::Choice(
            vec![
                Cow::Owned(QueryExpr::Parens(Box::new(Cow::Borrowed(expr)))),
                Cow::Borrowed(expr),
            ]
        )
    }

    pub fn if_stmt(
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

    pub fn and(lhs: QueryExpr<'a>, rhs: QueryExpr<'a>, meta: QueryMeta<'a>) -> QueryExpr<'a> {
        QueryExpr::BinExpr(BinOpQueryExpr {
            operator: "&&",
            lhs: Box::new(lhs),
            rhs: Box::new(rhs)
        }, meta)
    }

    pub const fn ident(capture: &'a str) -> QueryExpr<'a> {
        QueryExpr::Ident(QueryMeta::capture(capture))
    }
}