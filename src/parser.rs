use std::collections::HashMap;

use anyhow::Result;
use pest::iterators::Pair;
use pest::iterators::Pairs;
use pest::pratt_parser::Assoc;
use pest::pratt_parser::Op;
use pest::pratt_parser::PrattParser;
use pest::Parser;
use pest::RuleType;
use pest_derive::Parser;

#[derive(Debug, Clone, PartialEq)]
pub enum AstNode {
    // type, name, value
    Def(String, String, Expr),
    // type, name, dimensions
    // a vector of length 0 indicates a scalar
    DefEmpty(String, String, Vec<Expr>),
    // assignee = value
    Assign(Expr, Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // this vector may contain vectors
    // it's up to the compiler to verify the shape of the
    // structure
    VecLit(Vec<Expr>),
    Lit(String),
    Val(String, Vec<Expr>),
    NumOp {
        lhs: Box<Expr>,
        op: NumOp,
        rhs: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub enum NumOp {
    Add,
    Sub,
    Inv,
    Mul,
}

#[derive(Parser)]
#[grammar = "grammar.pest"] // relative to project `src`
pub struct LangPestParser;

pub struct LangParser {
    pub ast: Vec<AstNode>,
    pub fn_names: HashMap<String, u64>,
    pub entry_fn_name: String,
}

impl LangParser {
    pub fn parse(source: &str, name: &str) -> Result<Self> {
        let source = format!("{source}\n");
        let mut out = Self {
            ast: Vec::new(),
            fn_names: HashMap::new(),
            entry_fn_name: name.to_string(),
        };

        let pairs = LangPestParser::parse(Rule::program, &source)?;
        for pair in pairs {
            if let Some(node) = out.build_ast_node_from_pair(pair)? {
                out.ast.push(node);
            }
        }
        Ok(out)
    }

    fn mark_fn_call(&mut self, name: String) {
        let count = self.fn_names.entry(name).or_insert(0);
        *count += 1;
    }

    pub fn next_or_error<'a, T: RuleType>(pairs: &'a mut Pairs<T>) -> Result<Pair<'a, T>> {
        if let Some(n) = pairs.next() {
            Ok(n)
        } else {
            anyhow::bail!("Expected next token but found none")
        }
    }

    fn parse_def_type(pair: pest::iterators::Pair<Rule>) -> Result<String> {
        let def_type = pair.as_str().to_string();
        if def_type == "signal" || def_type == "static" {
            Ok(def_type)
        } else {
            Err(pest::error::Error::<()>::new_from_span(
                pest::error::ErrorVariant::CustomError {
                    message: "expected type static or signal".to_string(),
                },
                pair.as_span(),
            )
            .into())
        }
    }

    fn build_ast_node_from_pair(
        &mut self,
        pair: pest::iterators::Pair<Rule>,
    ) -> Result<Option<AstNode>> {
        match pair.as_rule() {
            Rule::def => {
                let mut pair = pair.into_inner();
                let def_type = Self::next_or_error(&mut pair)?;
                let def_type = Self::parse_def_type(def_type)?;
                let name = Self::next_or_error(&mut pair)?.as_str().to_string();
                let expr = Self::next_or_error(&mut pair)?;
                let expr = self.build_expr_from_pair(expr)?;
                Ok(Some(AstNode::Def(def_type, name, expr)))
            }
            Rule::def_empty => {
                let mut pair = pair.into_inner();
                let def_type = Self::next_or_error(&mut pair)?;
                let def_type = Self::parse_def_type(def_type)?;
                let name = Self::next_or_error(&mut pair)?.as_str().to_string();
                let mut dimensions = vec![];
                while let Some(v) = pair.next() {
                    let expr = self.build_expr_from_pair(v.clone())?;
                    if matches!(expr, Expr::VecLit(_)) {
                        return Err(pest::error::Error::<()>::new_from_span(
                            pest::error::ErrorVariant::CustomError {
                                message: "cannot specify dimension of variable using a vector literal\n    HINT: a 4x8 matrix is [4][8]"
                                    .to_string(),
                            },
                            v.as_span(),
                        )
                        .into());
                    }
                    dimensions.push(self.build_expr_from_pair(v)?);
                }
                Ok(Some(AstNode::DefEmpty(def_type, name, dimensions)))
            }
            Rule::assign => {
                let mut pair = pair.into_inner();
                let assignee = self.build_expr_from_pair(Self::next_or_error(&mut pair)?)?;
                let val = self.build_expr_from_pair(Self::next_or_error(&mut pair)?)?;
                Ok(Some(AstNode::Assign(assignee, val)))
            }
            Rule::EOI => Ok(None),
            _ => anyhow::bail!("unexpected line pair rule: {:?}", pair.as_rule()),
        }
    }

    fn build_expr_from_pair(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Expr> {
        match pair.as_rule() {
            Rule::literal_dec => Ok(Expr::Lit(pair.as_str().to_string())),
            Rule::vector_lit => {
                let mut pair = pair.into_inner();
                let mut vars = vec![];
                while let Some(v) = pair.next() {
                    vars.push(self.build_expr_from_pair(v)?);
                }
                Ok(Expr::VecLit(vars))
            }
            Rule::var => {
                let mut pair = pair.into_inner();
                let name = Self::next_or_error(&mut pair)?.as_str().to_string();
                let mut indices: Vec<Expr> = Vec::new();
                while let Some(v) = pair.next() {
                    let expr = self.build_expr_from_pair(v.clone())?;
                    // disallow vector literals in variable indices
                    if matches!(expr, Expr::VecLit(_)) {
                        return Err(pest::error::Error::<()>::new_from_span(
                            pest::error::ErrorVariant::CustomError {
                                message: "cannot access index of variable using a vector literal\n    HINT: remove any extra brackets"
                                    .to_string(),
                            },
                            v.as_span(),
                        )
                        .into());
                    }
                    indices.push(expr);
                }
                Ok(Expr::Val(name, indices))
            }
            Rule::atom => {
                let mut pair = pair.into_inner();
                let n = Self::next_or_error(&mut pair)?;
                match n.as_rule() {
                    // Rule::function_call => Ok(self.build_expr_from_pair(n)?),
                    Rule::varname => Ok(Expr::Val(n.as_str().to_string(), vec![])),
                    Rule::var => self.build_expr_from_pair(n),
                    Rule::literal_dec => Ok(Expr::Lit(n.as_str().to_string())),
                    _ => anyhow::bail!("invalid atom"),
                }
            }
            Rule::parenth => {
                let mut pair = pair.into_inner();
                let n = Self::next_or_error(&mut pair)?;
                self.build_expr_from_pair(n)
            }
            Rule::expr => {
                let mut pair = pair.into_inner();
                if pair.len() == 1 {
                    return self.build_expr_from_pair(Self::next_or_error(&mut pair)?);
                }
                let pratt = PrattParser::new()
                    .op(Op::infix(Rule::add, Assoc::Left) | Op::infix(Rule::sub, Assoc::Left))
                    .op(Op::infix(Rule::mul, Assoc::Left) | Op::infix(Rule::inv, Assoc::Left));
                pratt
                    .map_primary(|primary| self.build_expr_from_pair(primary))
                    .map_infix(|lhs, op, rhs| match op.as_rule() {
                        Rule::add => Ok(Expr::NumOp {
                            lhs: Box::new(lhs?),
                            op: NumOp::Add,
                            rhs: Box::new(rhs?),
                        }),
                        Rule::sub => Ok(Expr::NumOp {
                            lhs: Box::new(lhs?),
                            op: NumOp::Sub,
                            rhs: Box::new(rhs?),
                        }),
                        Rule::mul => Ok(Expr::NumOp {
                            lhs: Box::new(lhs?),
                            op: NumOp::Mul,
                            rhs: Box::new(rhs?),
                        }),
                        Rule::inv => Ok(Expr::NumOp {
                            lhs: Box::new(lhs?),
                            op: NumOp::Inv,
                            rhs: Box::new(rhs?),
                        }),
                        _ => unreachable!(),
                    })
                    .parse(pair)
            }
            unknown_expr => anyhow::bail!(
                "Unable to build expression, unexpected rule: {:?}",
                unknown_expr
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use anyhow::Result;

    use super::*;

    #[test]
    fn parse_simple_program() -> Result<()> {
        let program = "static v = 0

            signal x = 10
            signal y = 20 # test comment
            signal z = 30 / 2

            signal a = x*y + z
        ";

        let p = LangParser::parse(program, "test_program")?;
        let expected = vec![
            AstNode::Def(
                "static".to_string(),
                "v".to_string(),
                Expr::Lit("0".to_string()),
            ),
            AstNode::Def(
                "signal".to_string(),
                "x".to_string(),
                Expr::Lit("10".to_string()),
            ),
            AstNode::Def(
                "signal".to_string(),
                "y".to_string(),
                Expr::Lit("20".to_string()),
            ),
            AstNode::Def(
                "signal".to_string(),
                "z".to_string(),
                Expr::NumOp {
                    lhs: Box::new(Expr::Lit("30".to_string())),
                    op: NumOp::Inv,
                    rhs: Box::new(Expr::Lit("2".to_string())),
                },
            ),
            AstNode::Def(
                "signal".to_string(),
                "a".to_string(),
                Expr::NumOp {
                    lhs: Box::new(Expr::NumOp {
                        lhs: Box::new(Expr::Val("x".to_string(), vec![])),
                        op: NumOp::Mul,
                        rhs: Box::new(Expr::Val("y".to_string(), vec![])),
                    }),
                    rhs: Box::new(Expr::Val("z".to_string(), vec![])),
                    op: NumOp::Add,
                },
            ),
        ];
        assert_eq!(expected, p.ast);
        Ok(())
    }

    #[test]
    fn parse_val_assignment() -> Result<()> {
        let program = "
            static v: [10][20]
            v[0][0] = 99
            v[1][2] = 999

            static x = 10
            x = 88
        ";
        let p = LangParser::parse(program, "test_program")?;
        let expected = vec![
            AstNode::DefEmpty(
                "static".to_string(),
                "v".to_string(),
                vec![Expr::Lit("10".to_string()), Expr::Lit("20".to_string())],
            ),
            AstNode::Assign(
                Expr::Val(
                    "v".to_string(),
                    vec![Expr::Lit("0".to_string()), Expr::Lit("0".to_string())],
                ),
                Expr::Lit("99".to_string()),
            ),
            AstNode::Assign(
                Expr::Val(
                    "v".to_string(),
                    vec![Expr::Lit("1".to_string()), Expr::Lit("2".to_string())],
                ),
                Expr::Lit("999".to_string()),
            ),
            AstNode::Def(
                "static".to_string(),
                "x".to_string(),
                Expr::Lit("10".to_string()),
            ),
            AstNode::Assign(
                Expr::Val("x".to_string(), vec![]),
                Expr::Lit("88".to_string()),
            ),
        ];
        assert_eq!(expected, p.ast);
        Ok(())
    }

    #[test]
    fn parse_var_index_assign_error() -> Result<()> {
        let program = "
            y[[2]] = 4
        ";
        let r = LangParser::parse(program, "test_program");
        if let Err(v) = r {
            println!("{}", v);
        } else {
            let r = r.unwrap();
            println!("{:?}", r.ast);
            panic!("expected error assigning index of variable using vector literal");
        }
        Ok(())
    }

    #[test]
    fn parse_vec_literal() -> Result<()> {
        let program = "
            static v = [
                0,
                1,
                2,
                3,
                4
            ]
            ";
        let p = LangParser::parse(program, "test_program")?;
        let expected = vec![AstNode::Def(
            "static".to_string(),
            "v".to_string(),
            Expr::VecLit(vec![
                Expr::Lit("0".to_string()),
                Expr::Lit("1".to_string()),
                Expr::Lit("2".to_string()),
                Expr::Lit("3".to_string()),
                Expr::Lit("4".to_string()),
            ]),
        )];
        assert_eq!(expected, p.ast);
        Ok(())
    }

    #[test]
    fn parse_mat_literal() -> Result<()> {
        let program = "static v = [[0, 9], [1, 10], [2, 11], [3, 12], [4, 13]]";
        let p = LangParser::parse(program, "test_program")?;
        let expected = vec![AstNode::Def(
            "static".to_string(),
            "v".to_string(),
            Expr::VecLit(vec![
                Expr::VecLit(vec![Expr::Lit("0".to_string()), Expr::Lit("9".to_string())]),
                Expr::VecLit(vec![
                    Expr::Lit("1".to_string()),
                    Expr::Lit("10".to_string()),
                ]),
                Expr::VecLit(vec![
                    Expr::Lit("2".to_string()),
                    Expr::Lit("11".to_string()),
                ]),
                Expr::VecLit(vec![
                    Expr::Lit("3".to_string()),
                    Expr::Lit("12".to_string()),
                ]),
                Expr::VecLit(vec![
                    Expr::Lit("4".to_string()),
                    Expr::Lit("13".to_string()),
                ]),
            ]),
        )];
        assert_eq!(expected, p.ast);
        Ok(())
    }

    #[test]
    fn parse_indexed_var() -> Result<()> {
        let program = "
            signal y: [20][10][3]

            signal z = y[0][1][2]
        ";
        let p = LangParser::parse(program, "test_program")?;
        let expected = vec![
            AstNode::DefEmpty(
                "signal".to_string(),
                "y".to_string(),
                vec![
                    Expr::Lit("20".to_string()),
                    Expr::Lit("10".to_string()),
                    Expr::Lit("3".to_string()),
                ],
            ),
            AstNode::Def(
                "signal".to_string(),
                "z".to_string(),
                Expr::Val(
                    "y".to_string(),
                    vec![
                        Expr::Lit("0".to_string()),
                        Expr::Lit("1".to_string()),
                        Expr::Lit("2".to_string()),
                    ],
                ),
            ),
        ];
        assert_eq!(expected, p.ast);
        Ok(())
    }

    #[test]
    fn parse_indexed_var_error() -> Result<()> {
        let program = "
            signal y: [20][10][3]

            # it should be illegal to access an index
            # using a vector literal even though the
            # grammar technically allows it
            signal z = y[[0, 1, 2]]
        ";
        let r = LangParser::parse(program, "test_program");
        if let Err(v) = r {
            println!("{}", v);
        } else {
            let r = r.unwrap();
            println!("{:?}", r.ast);
            panic!("expected error accessing index using vector literal");
        }
        Ok(())
    }

    #[test]
    fn parse_empty_var_vec_literal_error() -> Result<()> {
        let program = "
            signal y: [[20, 30]]
        ";
        let r = LangParser::parse(program, "test_program");
        if let Err(v) = r {
            println!("{}", v);
        } else {
            let r = r.unwrap();
            println!("{:?}", r.ast);
            panic!("expected error instantiating empty variable using vector literal as dimension");
        }
        Ok(())
    }

    #[test]
    fn parse_empty_vars() -> Result<()> {
        let program = "static v

            signal x
            signal y: [20]
            signal z: [20][30]

            static l = 100

            # we'll test parentheses here too because why not
            signal a: [((l + v))]
        ";
        let p = LangParser::parse(program, "test_program")?;
        let expected = vec![
            AstNode::DefEmpty("static".to_string(), "v".to_string(), vec![]),
            AstNode::DefEmpty("signal".to_string(), "x".to_string(), vec![]),
            AstNode::DefEmpty(
                "signal".to_string(),
                "y".to_string(),
                vec![Expr::Lit("20".to_string())],
            ),
            AstNode::DefEmpty(
                "signal".to_string(),
                "z".to_string(),
                vec![Expr::Lit("20".to_string()), Expr::Lit("30".to_string())],
            ),
            AstNode::Def(
                "static".to_string(),
                "l".to_string(),
                Expr::Lit("100".to_string()),
            ),
            AstNode::DefEmpty(
                "signal".to_string(),
                "a".to_string(),
                vec![Expr::NumOp {
                    lhs: Box::new(Expr::Val("l".to_string(), vec![])),
                    op: NumOp::Add,
                    rhs: Box::new(Expr::Val("v".to_string(), vec![])),
                }],
            ),
        ];
        assert_eq!(expected, p.ast);
        Ok(())
    }

    #[test]
    fn parse_parentheses() -> Result<()> {
        let program = "static v = 0

            signal x = 10
            signal y = 20 # test comment
            signal z = (30)

            signal a = x * (y + ((((z - v)))))
        ";

        let p = LangParser::parse(program, "test_program")?;
        let expected = vec![
            AstNode::Def(
                "static".to_string(),
                "v".to_string(),
                Expr::Lit("0".to_string()),
            ),
            AstNode::Def(
                "signal".to_string(),
                "x".to_string(),
                Expr::Lit("10".to_string()),
            ),
            AstNode::Def(
                "signal".to_string(),
                "y".to_string(),
                Expr::Lit("20".to_string()),
            ),
            AstNode::Def(
                "signal".to_string(),
                "z".to_string(),
                Expr::Lit("30".to_string()),
            ),
            AstNode::Def(
                "signal".to_string(),
                "a".to_string(),
                Expr::NumOp {
                    lhs: Box::new(Expr::Val("x".to_string(), vec![])),
                    rhs: Box::new(Expr::NumOp {
                        lhs: Box::new(Expr::Val("y".to_string(), vec![])),
                        op: NumOp::Add,
                        rhs: Box::new(Expr::NumOp {
                            lhs: Box::new(Expr::Val("z".to_string(), vec![])),
                            op: NumOp::Sub,
                            rhs: Box::new(Expr::Val("v".to_string(), vec![])),
                        }),
                    }),
                    op: NumOp::Mul,
                },
            ),
        ];
        assert_eq!(expected, p.ast);
        Ok(())
    }
}
