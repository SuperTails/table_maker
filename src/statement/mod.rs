use crate::get_letter;
use crate::parse::{full_parse, BinaryOp, ParseNode, UnaryOp};
use crate::Variable;
use std::collections::HashSet;
use std::fmt;
use std::iter::once;
use std::str::FromStr;

mod pattern_statement;
mod proposition;
mod pattern_match;

pub use pattern_statement::*;
pub use proposition::*;
pub use pattern_match::*;


#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct StatementPath(Vec<usize>);

impl StatementPath {
    pub fn new() -> Self {
        StatementPath::default()
    }

    pub fn one(idx: usize) -> Self {
        StatementPath(vec![idx])
    }

    pub fn prepend(&mut self, other: &StatementPath) {
        let temp = std::mem::replace(&mut self.0, other.0.clone());
        self.0.extend(temp);
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Statement {
    Universal(Box<UniversalStatement>),
    Existential(Box<ExistentialStatement>),
    Binary(Box<BinaryExpression>),
    Unary(Box<UnaryExpression>),
    Variable(Variable),
}

impl Statement {
    pub fn get_sub_path<'a>(&'a self, path: &StatementPath) -> &'a Statement {
        self.get_sub_path_inner(&path.0)
    }

    fn get_sub_path_inner<'a>(&'a self, path: &[usize]) -> &'a Statement {
        if path.is_empty() {
            self
        } else {
            let idx = path[0];
            let tail = &path[1..];

            let lower = match (self, idx) {
                (Statement::Binary(b), 0) => &b.lhs,
                (Statement::Binary(b), 1) => &b.rhs,
                (Statement::Binary(_), i) => panic!("Invalid index {} for binary expression", i),
                (Statement::Unary(u), 0) => &u.inner,
                (Statement::Unary(_), i) => panic!("Invalid index {} for unary expression", i),
                _ => todo!(),
            };

            lower.get_sub_path_inner(tail)
        }
    }

    pub fn sub_path_mut<'a>(&'a mut self, path: &StatementPath) -> &'a mut Statement {
        self.sub_path_mut_inner(&path.0)
    }

    fn sub_path_mut_inner<'a>(&'a mut self, path: &[usize]) -> &'a mut Statement {
        if path.is_empty() {
            self
        } else {
            let idx = path[0];

            let lower = match (self, idx) {
                (Statement::Binary(b), 0) => &mut b.lhs,
                (Statement::Binary(b), 1) => &mut b.rhs,
                (Statement::Binary(_), i) => panic!("Invalid index {} for binary expression", i),
                (Statement::Unary(u), 0) => &mut u.inner,
                (Statement::Unary(_), i) => panic!("Invalid index {} for unary expression", i),
                _ => todo!(),
            };

            lower.sub_path_mut_inner(&path[1..])
        }
    }


    pub fn variables(&self) -> HashSet<&Variable> {
        match self {
            Statement::Universal(u) => {
                let mut m = u.inner.variables();
                m.insert(&u.bound);
                m
            }
            Statement::Existential(u) => {
                let mut m = u.inner.variables();
                m.insert(&u.bound);
                m
            }
            Statement::Binary(b) => b
                .lhs
                .variables()
                .union(&b.rhs.variables())
                .copied()
                .collect(),
            Statement::Unary(u) => u.inner.variables(),
            Statement::Variable(v) => vec![v].into_iter().collect(),
        }
    }

    pub fn bound_variables(&self) -> std::vec::IntoIter<&Variable> {
        match self {
            Statement::Universal(u) => vec![&u.bound].into_iter(),
            Statement::Existential(e) => vec![&e.bound].into_iter(),
            Statement::Binary(b) => b
                .lhs
                .bound_variables()
                .chain(b.rhs.bound_variables())
                .collect::<Vec<_>>()
                .into_iter(),
            Statement::Unary(u) => u.inner.bound_variables(),
            Statement::Variable(_) => vec![].into_iter(),
        }
    }

    pub fn unbound_variables(&self) -> HashSet<&Variable> {
        let mut v = self.variables();
        for bv in self.bound_variables() {
            v.remove(bv);
        }
        v
    }

    pub fn generate_table(&self, name: &str) {
        let variables = self.unbound_variables();

        if variables.is_empty() {
            println!(
                "({}) <-> {}",
                name,
                get_letter(self.evaluate(&|_| unreachable!()))
            );
        } else {
            let rows = 1 << variables.len();
            let mut width = 0;
            for var in variables.iter() {
                width += 1 + var.0.len();
                print!("|{}", var.0);
            }
            width += 2 + name.len();
            println!("|{}|", name);
            println!("{:-^w$}", "", w = width);

            for row in (0..rows).rev() {
                let get_value = |var: &str| -> bool {
                    let idx = variables
                        .iter()
                        .enumerate()
                        .find(|(_, v)| v.0 == var)
                        .unwrap()
                        .0;
                    (row >> (variables.len() - 1 - idx)) & 1 != 0
                };

                for var in variables.iter() {
                    print!("|{:^w$}", get_letter(get_value(&var.0)), w = var.0.len());
                }
                println!(
                    "|{:^w$}|",
                    get_letter(self.evaluate(&get_value)),
                    w = name.len()
                );
            }
        }
    }

    pub fn substatements(
        &self,
    ) -> impl Iterator<
        Item = (
            (&Statement, StatementPath),
            Option<(&Statement, StatementPath)>,
        ),
    > {
        once(((self, StatementPath::new()), None)).chain(self.proper_substatements())
    }

    /// This does not include the full statement itself
    pub fn proper_substatements(
        &self,
    ) -> impl Iterator<
        Item = (
            (&Statement, StatementPath),
            Option<(&Statement, StatementPath)>,
        ),
    > {
        let result = match self {
            Statement::Binary(b) => {
                let BinaryExpression { lhs, rhs, .. } = &**b;

                let lhs_head = (lhs, StatementPath::one(0));
                let rhs_head = (rhs, StatementPath::one(1));

                let rhs_tail = (rhs, StatementPath::one(1));
                let lhs_tail = (lhs, StatementPath::one(0));

                vec![(lhs_head, Some(rhs_tail)), (rhs_head, Some(lhs_tail))]
            }
            Statement::Unary(u) => {
                let UnaryExpression { inner, .. } = &**u;

                vec![((inner, StatementPath::new()), None)]
            }
            Statement::Existential(e) => {
                let ExistentialStatement { inner, .. } = &**e;

                vec![((inner, StatementPath::new()), None)]
            }
            Statement::Universal(u) => {
                let UniversalStatement { inner, .. } = &**u;

                vec![((inner, StatementPath::new()), None)]
            }
            Statement::Variable(_) => vec![],
        };

        result.into_iter()
    }

    pub fn evaluate<F>(&self, f: &F) -> bool
    where
        F: Fn(&str) -> bool,
    {
        match self {
            Statement::Binary(b) => {
                let BinaryExpression { op, lhs, rhs } = &**b;
                op.apply(lhs.evaluate(f), rhs.evaluate(f))
            }
            Statement::Unary(u) => {
                let UnaryExpression { op, inner } = &**u;
                op.apply(inner.evaluate(f))
            }
            Statement::Variable(v) => f(&v.0),
            _ => todo!(),
        }
    }
}

fn pathed_substs<'a>(
    statement: &'a Statement,
    path: &StatementPath,
) -> impl Iterator<
    Item = (
        (&'a Statement, StatementPath),
        Option<(&'a Statement, StatementPath)>,
    ),
> {
    let mut substs = statement.substatements().collect::<Vec<_>>();

    for ((_, p), tail) in substs.iter_mut() {
        p.prepend(path);
        if let Some((_, p)) = tail {
            p.prepend(path);
        }
    }

    substs.into_iter()
}

impl FromStr for Statement {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Ok(Statement::from(full_parse(s)?))
    }
}

#[doc(hidden)]
impl From<ParseNode<'_>> for Statement {
    fn from(node: ParseNode<'_>) -> Statement {
        match node {
            ParseNode::BinaryOperation { lhs, rhs, op } => {
                Statement::Binary(Box::new(BinaryExpression {
                    lhs: (*lhs).into(),
                    rhs: (*rhs).into(),
                    op,
                }))
            }
            ParseNode::UnaryOperation { inner, op } => {
                Statement::Unary(Box::new(UnaryExpression {
                    inner: (*inner).into(),
                    op,
                }))
            }
            ParseNode::Variable(v) => Statement::Variable(Variable(v.into())),
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Binary(b) => write!(f, "{}", b),
            Statement::Unary(u) => write!(f, "{}", u),
            // TODO: Display properly
            Statement::Variable(v) => write!(f, "{}", v.0),
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UniversalStatement {
    pub bound: Variable,
    pub inner: Statement,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExistentialStatement {
    pub bound: Variable,
    pub inner: Statement,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BinaryExpression {
    pub lhs: Statement,
    pub rhs: Statement,
    pub op: BinaryOp,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct UnaryExpression {
    pub inner: Statement,
    pub op: UnaryOp,
}

impl fmt::Display for BinaryExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.op {
            BinaryOp::Conjunction => write!(f, "({} ^ {})", self.lhs, self.rhs),
            BinaryOp::Disjunction => write!(f, "({} V {})", self.lhs, self.rhs),
            BinaryOp::Equivalence => write!(f, "({} == {})", self.lhs, self.rhs),
            BinaryOp::Implication => write!(f, "({} -> {})", self.lhs, self.rhs),
        }
    }
}

impl fmt::Display for UnaryExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.op {
            UnaryOp::Negation => write!(f, "!{}", self.inner),
        }
    }
}

#[cfg(test)]
mod tests {
    // TODO:
}
