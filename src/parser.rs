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
    SignalDef(String, Expr),
    StaticDef(String, Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
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

        match LangPestParser::parse(Rule::program, &source) {
            Ok(pairs) => {
                let ast = out.build_ast_from_lines(pairs);
                if let Err(e) = ast {
                    anyhow::bail!("error building program ast: {e}");
                }
            }
            Err(e) => {
                return Err(anyhow::anyhow!(e));
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

    fn build_ast_from_lines(&mut self, pairs: Pairs<Rule>) -> Result<()> {
        for pair in pairs {
            match pair.as_rule() {
                Rule::stmt => {
                    let mut pair = pair.into_inner();
                    let next = Self::next_or_error(&mut pair)?;
                    let ast = self.build_ast_from_pair(next)?;
                    self.ast.push(ast);
                }
                Rule::EOI => {}
                _ => anyhow::bail!("unexpected line pair rule: {:?}", pair.as_rule()),
            }
        }
        Ok(())
    }

    fn build_ast_from_pair(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<AstNode> {
        match pair.as_rule() {
            Rule::static_def => {
                let mut pair = pair.into_inner();
                let name = Self::next_or_error(&mut pair)?.to_string();
                let expr = Self::next_or_error(&mut pair)?;
                Ok(AstNode::StaticDef(name, self.build_expr_from_pair(expr)?))
            }
            Rule::signal_def => {
                let mut pair = pair.into_inner();
                let name = Self::next_or_error(&mut pair)?.to_string();
                let expr = Self::next_or_error(&mut pair)?;
                Ok(AstNode::SignalDef(name, self.build_expr_from_pair(expr)?))
            }
            _ => unreachable!(),
        }
    }

    fn build_expr_from_pair(&mut self, pair: pest::iterators::Pair<Rule>) -> Result<Expr> {
        match pair.as_rule() {
            Rule::literal_dec => Ok(Expr::Lit(pair.to_string())),
            Rule::atom => {
                let mut pair = pair.into_inner();
                let n = Self::next_or_error(&mut pair)?;
                match n.as_rule() {
                    // Rule::function_call => Ok(self.build_expr_from_pair(n)?),
                    Rule::varname => Ok(Expr::Val(n.to_string(), vec![])),
                    // Rule::var_indexed => {
                    //     let mut pair = n.into_inner();
                    //     let name = Self::next_or_error(&mut pair)?.to_string();
                    //     let mut indices: Vec<Expr> = Vec::new();
                    //     for v in pair {
                    //         indices.push(self.build_expr_from_pair(v)?);
                    //     }
                    //     Ok(Expr::Val(name, indices))
                    // }
                    Rule::literal_dec => Ok(Expr::Lit(n.to_string())),
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
            AstNode::StaticDef("v".to_string(), Expr::Lit("0".to_string())),
            AstNode::SignalDef("x".to_string(), Expr::Lit("10".to_string())),
            AstNode::SignalDef("y".to_string(), Expr::Lit("20".to_string())),
            AstNode::SignalDef(
                "z".to_string(),
                Expr::NumOp {
                    lhs: Box::new(Expr::Lit("30".to_string())),
                    op: NumOp::Inv,
                    rhs: Box::new(Expr::Lit("2".to_string())),
                },
            ),
            AstNode::SignalDef(
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
    fn parse_parentheses() -> Result<()> {
        let program = "static v = 0

            signal x = 10
            signal y = 20 # test comment
            signal z = (30)

            signal a = x * (y + ((((z - v)))))
        ";

        let p = LangParser::parse(program, "test_program")?;
        let expected = vec![
            AstNode::StaticDef("v".to_string(), Expr::Lit("0".to_string())),
            AstNode::SignalDef("x".to_string(), Expr::Lit("10".to_string())),
            AstNode::SignalDef("y".to_string(), Expr::Lit("20".to_string())),
            AstNode::SignalDef("z".to_string(), Expr::Lit("30".to_string())),
            AstNode::SignalDef(
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
