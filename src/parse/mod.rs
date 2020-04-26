mod token;

use std::collections::BTreeSet;
use token::{tokenize, Token};

/*
 * A => B => C
 *
 * (A => B) => C
 *
 */

/// Guaranteed to not contain parenthesis/brackets
#[derive(Debug, PartialEq, Eq, Clone)]
enum GroupedToken<'a> {
    Group(Vec<GroupedToken<'a>>),
    Token(Token<'a>),
}

impl PartialEq<Token<'_>> for GroupedToken<'_> {
    fn eq(&self, other: &Token<'_>) -> bool {
        if let GroupedToken::Token(t) = self {
            t == other
        } else {
            false
        }
    }
}

fn group<'a>(input: &[Token<'a>]) -> Result<GroupedToken<'a>, String> {
    let mut result = Vec::new();
    let mut paren_count = 0;
    let mut paren_start = 0;

    for (idx, token) in input.iter().copied().enumerate() {
        match token {
            Token::OpenBracket => {
                if paren_count == 0 {
                    paren_start = idx + 1;
                }
                paren_count += 1;
            }
            Token::CloseBracket if paren_count == 0 => return Err(format!("Unexpected closing parenthesis at token {}", idx)),
            Token::CloseBracket => {
                paren_count -= 1;
                if paren_count == 0 {
                    result.push(group(&input[paren_start..idx])?);
                }
            }
            _ if paren_count == 0 => result.push(GroupedToken::Token(token)),
            _ => {}
        }
    }

    Ok(GroupedToken::Group(result))
}

fn parse<'a>(input: &[Token<'a>]) -> Result<ParseNode<'a>, String> {
    if let GroupedToken::Group(g) = group(input)? {
        parse_inner(&g, 0)
    } else {
        unreachable!()
    }
}

/* Precedence:
 *
 * 4. Identifier/Group
 * 3. Negation
 * 2. Conjunction
 * 1. Disjunction
 * 0. Arrow, Double Arrow
 */
fn parse_inner<'a>(input: &[GroupedToken<'a>], level: usize) -> Result<ParseNode<'a>, String> {
    if level == 4 {
        return if input.is_empty() {
            Err("Empty input".to_string())
        } else if input.len() != 1 {
            Err("More than one consecutive identifier/group".to_string())
        } else {
            match &input[0] {
                GroupedToken::Token(Token::Variable(v)) => Ok(ParseNode::Variable(v)),
                GroupedToken::Token(t) => Err(format!("Invalid token '{:?}'", t)),
                GroupedToken::Group(g) => parse_inner(g, 0),
            }
        };
    }

    const TOKENS: [&[Token]; 4] = [
        &[Token::RightArrow, Token::DoubleArrow],
        &[Token::Disjunction],
        &[Token::Conjunction],
        &[Token::Negation],
    ];

    let found = {
        let mapper = |(i, t): (usize, &GroupedToken<'a>)| -> Option<(usize, Token<'a>)> {
            if let GroupedToken::Token(t) = t {
                if TOKENS[level].iter().any(|tok| tok == t) {
                    Some((i, *t))
                } else {
                    None
                }
            } else {
                None
            }
        };

        if level == 3 {
            input.iter().enumerate().filter_map(mapper).next()
        } else {
            input.iter().enumerate().rev().filter_map(mapper).next()
        }
    };

    if let Some((idx, found)) = found {
        if found == Token::Negation {
            let rhs = &input[idx + 1..];
            let op = UnaryOp::Negation;
            Ok(ParseNode::UnaryOperation {
                op,
                inner: Box::new(parse_inner(rhs, level)?),
            })
        } else {
            let lhs = &input[0..idx];
            let rhs = &input[idx + 1..];

            let op = match found {
                Token::RightArrow => BinaryOp::Implication,
                Token::DoubleArrow => BinaryOp::Equivalence,
                Token::Disjunction => BinaryOp::Disjunction,
                Token::Conjunction => BinaryOp::Conjunction,
                _ => panic!("Invalid found: {:?}", found),
            };

            Ok(ParseNode::BinaryOperation {
                op,
                lhs: Box::new(parse_inner(lhs, level)?),
                rhs: Box::new(parse_inner(rhs, level)?),
            })
        }
    } else {
        parse_inner(input, level + 1)
    }
}

pub fn full_parse(input: &str) -> Result<ParseNode, String> {
    parse(&tokenize(input)?)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BinaryOp {
    Conjunction,
    Disjunction,
    Implication,
    Equivalence,
}

impl BinaryOp {
    pub fn apply(self, lhs: bool, rhs: bool) -> bool {
        match self {
            BinaryOp::Conjunction => lhs && rhs,
            BinaryOp::Disjunction => lhs || rhs,
            BinaryOp::Implication => !lhs || rhs,
            BinaryOp::Equivalence => lhs == rhs,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum UnaryOp {
    Negation,
}

impl UnaryOp {
    pub fn apply(self, inner: bool) -> bool {
        match self {
            UnaryOp::Negation => !inner,
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseNode<'a> {
    Variable(&'a str),
    UnaryOperation {
        inner: Box<ParseNode<'a>>,
        op: UnaryOp,
    },
    BinaryOperation {
        lhs: Box<ParseNode<'a>>,
        rhs: Box<ParseNode<'a>>,
        op: BinaryOp,
    },
}

impl<'a> ParseNode<'a> {
    pub fn get_variables(&self) -> BTreeSet<&'a str> {
        match self {
            ParseNode::Variable(v) => std::iter::once(*v).collect(),
            ParseNode::UnaryOperation { inner, .. } => inner.get_variables(),
            ParseNode::BinaryOperation { lhs, rhs, .. } => {
                let mut l = lhs.get_variables();
                l.extend(rhs.get_variables().into_iter());
                l
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_parse() {
        assert_eq!(full_parse("a"), Ok(ParseNode::Variable("a")));
    }
}
