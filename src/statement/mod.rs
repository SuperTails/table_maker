use crate::get_letter;
use crate::parse::{full_parse, BinaryOp, ParseNode, UnaryOp};
use crate::Variable;
use std::collections::HashSet;
use std::fmt;
use std::iter::once;
use std::str::FromStr;
use lazy_static::lazy_static;

mod pattern_statement;
mod pattern_match;

pub use pattern_statement::*;
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Statement {
    Quantification(Box<QuantiStatement>),
    FuncApplication(FuncApplication),
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
                (Statement::FuncApplication(b), idx) => &b.args()[idx],
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
                (Statement::FuncApplication(b), idx) => &mut b.args_mut()[idx],
                _ => todo!(),
            };

            lower.sub_path_mut_inner(&path[1..])
        }
    }


    pub fn variables(&self) -> HashSet<&Variable> {
        match self {
            Statement::Quantification(u) => {
                let mut m = u.inner.variables();
                m.insert(&u.bound);
                m
            }
            Statement::FuncApplication(b) => {
                let mut variables = HashSet::new();
                for arg in b.args() {
                    variables.extend(arg.variables().iter().copied());
                }
                variables
            }
            Statement::Variable(v) => vec![v].into_iter().collect(),
        }
    }

    pub fn bound_variables(&self) -> std::vec::IntoIter<&Variable> {
        match self {
            Statement::Quantification(u) => vec![&u.bound].into_iter(),
            Statement::FuncApplication(b) => {
                b.args().iter().flat_map(|b| b.bound_variables()).collect::<Vec<_>>().into_iter()
            }
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
                get_letter(self.evaluate(&|_| unreachable!()).unwrap())
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
                    get_letter(self.evaluate(&get_value).unwrap()),
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
            Vec<(&Statement, StatementPath)>,
        ),
    > {
        once(((self, StatementPath::new()), Vec::new())).chain(self.proper_substatements())
    }

    /// This does not include the full statement itself
    pub fn proper_substatements(
        &self,
    ) -> impl Iterator<
        Item = (
            (&Statement, StatementPath),
            Vec<(&Statement, StatementPath)>,
        ),
    > {
        let result = match self {
            Statement::FuncApplication(f) => {
                f.args
                    .iter()
                    .enumerate()
                    .map(|(arg_idx, arg)| {
                        let current = (arg, StatementPath::one(arg_idx));
                        let others = f.args
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| *i != arg_idx)
                            .map(|(i, a)| (a, StatementPath::one(i)))
                            .collect();

                        (current, others)
                    })
                    .collect()
            }
            Statement::Quantification(e) => {
                let QuantiStatement { inner, .. } = &**e;

                vec![((inner, StatementPath::new()), Vec::new())]
            }
            Statement::Variable(_) => vec![],
        };

        result.into_iter()
    }

    pub fn evaluate<F>(&self, f: &F) -> Option<bool>
    where
        F: Fn(&str) -> bool,
    {
        match self {
            Statement::FuncApplication(app) => {
                let eval = app.function().evaluator()?;
                let args = app
                    .args()
                    .iter()
                    .map(|arg| arg.evaluate(f))
                    .collect::<Option<Vec<bool>>>()?;

                Some((eval)(&args))
            }
            Statement::Variable(v) => Some(f(&v.0)),
            _ => todo!(),
        }
    }
}

pub fn pathed_substs<'a>(
    statement: &'a Statement,
    path: &StatementPath,
) -> impl Iterator<
    Item = (
        (&'a Statement, StatementPath),
        Vec<(&'a Statement, StatementPath)>,
    ),
> {
    let mut substs = statement.substatements().collect::<Vec<_>>();

    for ((_, p), tail) in substs.iter_mut() {
        p.prepend(path);
        for (_, p) in tail {
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
                let def = match op {
                    BinaryOp::Conjunction => &*CONJUNCTION,
                    BinaryOp::Disjunction => &*DISJUNCTION,
                    BinaryOp::Equivalence => &*EQUIVALENCE,
                    BinaryOp::Implication => &*IMPLICATION,
                };
                Statement::FuncApplication(FuncApplication::binary((*lhs).into(), (*rhs).into(), def))
            }
            ParseNode::UnaryOperation { inner, op } => {
                let def = match op {
                    UnaryOp::Negation => &*NEGATION,
                };
                Statement::FuncApplication(FuncApplication::unary((*inner).into(), def))
            }
            ParseNode::Quantification { universal, bound, inner } => {
                let bound = Variable(bound.into());
                Statement::Quantification(Box::new(QuantiStatement {
                    bound,
                    inner: (*inner).into(),
                    universal,
                }))
            }
            ParseNode::Variable(v) => Statement::Variable(Variable(v.into())),
        }
    }
}

impl fmt::Display for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::FuncApplication(a) => write!(f, "{:?}", a),
            // TODO: Display properly
            Statement::Variable(v) => write!(f, "{}", v.0),
            _ => todo!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QuantiStatement {
    pub bound: Variable,
    pub inner: Statement,
    pub universal: bool,
}

pub struct FuncDefinition {
    arity: usize,
    evaluator: Option<Box<dyn Fn(&[bool]) -> bool + Sync>>,
    expander: Option<Box<dyn Fn(&[Statement]) -> Statement + Sync>>,
}

impl FuncDefinition {
    fn as_ptr_tuple(&self) -> (usize, Option<usize>, Option<usize>) {
        (
            self.arity,
            self.evaluator.as_deref().map(|e| &*e as *const _ as *const () as usize),
            self.expander.as_deref().map(|e| &*e as *const _ as *const () as usize),
        )
    }
}

impl PartialEq for FuncDefinition {
    fn eq(&self, other: &Self) -> bool {
        self.as_ptr_tuple() == other.as_ptr_tuple()
    }
}

impl Eq for FuncDefinition {}

impl PartialOrd for FuncDefinition {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.as_ptr_tuple().partial_cmp(&other.as_ptr_tuple())
    }
}

impl Ord for FuncDefinition {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.as_ptr_tuple().cmp(&other.as_ptr_tuple())
    }
}

impl std::hash::Hash for FuncDefinition {
    fn hash<H>(&self, state: &mut H)
    where
        H: std::hash::Hasher
    {
        self.as_ptr_tuple().hash(state)
    }
}

impl fmt::Debug for FuncDefinition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FuncDefinition {{ arity: {}, evaluator: {}, expander: {} }}",
            self.arity,
            if self.evaluator.is_some() { "Some" } else { "None" },
            if self.expander.is_some() { "Some" } else { "None" },
        )
    }
}

impl FuncDefinition {
    pub fn arity(&self) -> usize {
        self.arity
    }

    pub fn evaluator(&self) -> Option<&(dyn Fn(&[bool]) -> bool + Sync)> {
        self.evaluator.as_deref()
    }

    pub fn expander(&self) -> Option<&(dyn Fn(&[Statement]) -> Statement + Sync)> {
        self.expander.as_deref()
    }
}

// TODO: These can probably all be represented in terms of
// negation and either conjunction or disjunction
// This also means an expander could be made for some of them
lazy_static! {
    pub static ref NEGATION: FuncDefinition = FuncDefinition {
        arity: 1,
        evaluator: Some(Box::new(|args| { assert_eq!(args.len(), 1); !args[0] })),
        expander: None,
    };

    pub static ref CONJUNCTION: FuncDefinition = FuncDefinition {
        arity: 2,
        evaluator: Some(Box::new(|args| { assert_eq!(args.len(), 2); args[0] && args[1] })),
        expander: None,
    };

    pub static ref DISJUNCTION: FuncDefinition = FuncDefinition {
        arity: 2,
        evaluator: Some(Box::new(|args| { assert_eq!(args.len(), 2); args[0] || args[1] })),
        expander: None,
    };

    pub static ref IMPLICATION: FuncDefinition = FuncDefinition {
        arity: 2,
        evaluator: Some(Box::new(|args| { assert_eq!(args.len(), 2); !args[0] || args[1] })),
        expander: None,
    };

    pub static ref EQUIVALENCE: FuncDefinition = FuncDefinition {
        arity: 2,
        evaluator: Some(Box::new(|args| { assert_eq!(args.len(), 2); args[0] == args[1] })),
        expander: None,
    };
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FuncApplication {
    args: Vec<Statement>,
    function: &'static FuncDefinition,
}

impl FuncApplication {
    pub fn new(args: Vec<Statement>, function: &'static FuncDefinition) -> Self {
        assert_eq!(args.len(), function.arity());

        FuncApplication {
            function,
            args,
        }
    }

    pub fn unary(arg: Statement, function: &'static FuncDefinition) -> Self {
        FuncApplication::new(vec![arg], function)
    }

    pub fn binary(lhs: Statement, rhs: Statement, function: &'static FuncDefinition) -> Self {
        FuncApplication::new(vec![lhs, rhs], function)
    }

    pub fn args(&self) -> &[Statement] {
        &self.args
    }

    pub fn args_mut(&mut self) -> &mut [Statement] {
        &mut self.args
    }

    pub fn function(&self) -> &'static FuncDefinition {
        &self.function
    }
}

#[cfg(test)]
mod tests {
    // TODO:
}
