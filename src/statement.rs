use crate::get_letter;
use crate::parse::{full_parse, BinaryOp, ParseNode, UnaryOp};
use crate::substitution::Substitution;
use crate::Variable;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::convert::TryFrom;
use std::fmt;
use std::iter::once;
use std::ops::Deref;
use std::str::FromStr;

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

// Note that in any of these structs, no variable may be bound twice

macro_rules! maybe_match {
    ($p:path = $e:expr) => {
        if let $p(inner) = $e {
            Some(inner)
        } else {
            None
        }
    };
}

impl fmt::Display for PatternStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Pattern: {{ {} }}", self.0)
    }
}

/// A pattern statement can be matched on, and always has
/// at least one unbound variable
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(transparent)]
pub struct PatternStatement(Statement);

impl PatternStatement {
    fn is_valid_pattern(s: &Statement) -> bool {
        !s.unbound_variables().is_empty()
    }

    /// Returns `None` if the given statement has no unbound variables
    pub fn new_ref(s: &Statement) -> Option<&PatternStatement> {
        if Self::is_valid_pattern(s) {
            // This must be safe because `PatternStatement` is `repr(transparent)`,
            // and the only restriction on the inner statement is that `s` is a valid pattern
            Some(unsafe { &*(s as *const Statement as *const PatternStatement) })
        } else {
            None
        }
    }

    /// Returns `None` if the given statement has no unbound variables
    pub fn new(s: Statement) -> Option<PatternStatement> {
        if Self::is_valid_pattern(&s) {
            Some(PatternStatement(s))
        } else {
            None
        }
    }

    /// Returns the set of *every* possible group of pattern-statement pairs
    /// Each 'statement' in the return value is represented by its index in the argument,
    /// and then path in that statement
    fn get_potential_sets<'a>(
        patterns: &HashSet<&'a PatternStatement>,
        statements: &[Statement],
    ) -> HashSet<BTreeMap<&'a PatternStatement, (usize, StatementPath)>> {
        let statements = statements
            .iter()
            .enumerate()
            .map(|(idx, st)| ((idx, StatementPath::default()), st))
            .collect();

        Self::get_potential_sets_inner(patterns, &statements)
    }

    fn get_potential_sets_inner<'a>(
        patterns: &HashSet<&'a PatternStatement>,
        statements: &HashMap<(usize, StatementPath), &Statement>,
    ) -> HashSet<BTreeMap<&'a PatternStatement, (usize, StatementPath)>> {
        if patterns.is_empty() {
            // Technically, "every" pattern matched, so we do have one result
            once(BTreeMap::new()).collect()
        } else {
            let mut result = HashSet::new();

            for pat in patterns.iter() {
                // The set of patterns not already matched with
                let mut remaining_patterns = patterns.clone();
                remaining_patterns.remove(pat);

                for (full_path, st) in statements.iter() {
                    for ((_, head_path), tail) in pathed_substs(st, &full_path.1) {
                        // The set of statements not already matched with
                        let mut remaining_statements = statements.clone();
                        remaining_statements.remove(full_path).unwrap();

                        if let Some((tail_st, tail_path)) = tail {
                            remaining_statements.insert((full_path.0, tail_path), tail_st);
                        }

                        // Get the other answers for whatever we haven't used yet
                        let other_matches = Self::get_potential_sets_inner(
                            &remaining_patterns,
                            &remaining_statements,
                        );

                        for mut other in other_matches {
                            // Add in the pair we already selected
                            other.insert(*pat, (full_path.0, head_path.clone()));

                            result.insert(other);
                        }
                    }
                }
            }

            result
        }
    }

    /// Assume P is the set of pattern statements
    /// Assume S is the set of normal statements
    /// The goal of multimatch is to find all sets M containing of pattern-statement pairs,
    /// * Each pattern appears exactly once in an element of M
    /// * Each statement appears at most one time in an element of M
    /// * Every element m of M matches
    /// * The matches are coherent
    pub fn try_multimatch<'a>(
        patterns: HashSet<&'a PatternStatement>,
        statements: &[Statement],
    ) -> HashSet<PatternSetMatch<'a>> {
        // Each pattern must appear exactly once,
        // which means that we must have enough
        // statements to match against
        if statements.len() < patterns.len() {
            return HashSet::new();
        }

        Self::get_potential_sets(&patterns, &statements)
            .into_iter()
            .filter(|potential| {
                // Determine the overall substitution for this set of matchups
                let overall =
                    potential
                        .iter()
                        .try_fold(Substitution::new(), |overall, (p1, st_path)| {
                            let st = statements[st_path.0].get_sub_path(&st_path.1);

                            let matched = p1.try_toplevel_match(st)?;
                            overall.try_merge(&matched)
                        });

                // Only use matchup sets which result in a sensible substitution
                overall.is_some()
            })
            .collect()
    }

    /// Returns the substitution that may result if this pattern
    /// and the statement are directly compared, i.e. the whole statement is always used
    ///
    /// # Example
    /// ```
    /// # use table_maker::Variable;
    /// # use table_maker::statement::{Statement, PatternStatement};
    /// # use table_maker::substitution::Substitution;
    /// # use std::collections::HashMap;
    /// let pattern = "p -> q".parse::<PatternStatement>().unwrap();
    /// let statement = "[a ^ b] -> [c -> d]".parse::<Statement>().unwrap();
    ///
    /// let pat_match = pattern.try_toplevel_match(&statement).unwrap();
    ///
    /// let expected = Substitution::parse_owned("
    ///     p: a ^ b
    ///     q: c -> d
    /// ").unwrap();
    ///
    /// # let expected = expected.iter().map(|(v, s)| (v, s.clone())).collect();
    ///
    ///
    /// assert_eq!(pat_match.0, expected);
    /// ```
    pub fn try_toplevel_match<'a, 'b>(
        &'a self,
        statement: &'b Statement,
    ) -> Option<Substitution<'a>> {
        let mut matches = Substitution::new();

        // TODO: Determine if a statement can be matched by a pattern in multiple ways

        match &self.0 {
            Statement::Variable(v) => {
                // A variable will match anything
                matches.try_insert(v, statement.clone())?;
            }
            Statement::Binary(b1) => {
                let b2 = maybe_match!(Statement::Binary = statement)?;

                let BinaryExpression {
                    lhs: l1,
                    rhs: r1,
                    op: op1,
                } = &**b1;
                let BinaryExpression {
                    lhs: l2,
                    rhs: r2,
                    op: op2,
                } = &**b2;

                if op1 == op2 {
                    let left_matches = PatternStatement::new_ref(l1)
                        .unwrap()
                        .try_toplevel_match(l2)?;
                    let right_matches = PatternStatement::new_ref(r1)
                        .unwrap()
                        .try_toplevel_match(r2)?;

                    println!("Left matches: {}", left_matches);
                    println!("Right matches: {}", right_matches);

                    matches = matches.try_merge(&left_matches)?;
                    matches = matches.try_merge(&right_matches)?;
                } else {
                    // TODO: Is this the correct behavior?
                    return None;
                }
            }
            Statement::Unary(u1) => {
                let u2 = maybe_match!(Statement::Unary = statement)?;
                let UnaryExpression { inner: i1, op: op1 } = &**u1;
                let UnaryExpression {
                    inner: inner_statement,
                    op: op2,
                } = &**u2;

                if op1 == op2 {
                    let inner_pattern = PatternStatement::new_ref(i1).unwrap();
                    let new_matches = inner_pattern.try_toplevel_match(inner_statement)?;

                    matches = matches.try_merge(&new_matches)?;
                } else {
                    // TODO: Is this the correct behavior?
                    return None;
                }
            }
            _ => todo!("{:?}", self),
        }

        Some(matches)
    }
}

impl FromStr for PatternStatement {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        PatternStatement::new(s.parse::<Statement>()?)
            .ok_or_else(|| "No unbound variables".to_string())
    }
}

pub type PatternSetMatch<'a> = BTreeMap<&'a PatternStatement, (usize, StatementPath)>;

#[doc(hidden)]
impl TryFrom<ParseNode<'_>> for PatternStatement {
    type Error = ();

    fn try_from(value: ParseNode<'_>) -> Result<Self, Self::Error> {
        PatternStatement::new(Statement::from(value)).ok_or(())
    }
}

impl Deref for PatternStatement {
    type Target = Statement;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A Proposition is a Statement with no unbound variables
pub struct Proposition {
    bindings: HashMap<Variable, bool>,
    statement: Statement,
}

impl Proposition {
    pub fn new(
        bindings: HashMap<Variable, bool>,
        statement: Statement,
    ) -> Result<Proposition, String> {
        let unbound = statement.unbound_variables();
        let newly_bound = bindings.keys().collect::<HashSet<_>>();

        let missing = &unbound - &newly_bound;
        if missing.is_empty() {
            Ok(Proposition {
                bindings,
                statement,
            })
        } else {
            Err(format!("Unbound variables {:?}", missing))
        }
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn conflicting_match() {
        // In order for this pattern to match, `p` would have to be
        // both `a` and `b`, which is impossible
        let pattern = "p ^ p".parse::<PatternStatement>().unwrap();
        let statements = vec!["a ^ b".parse::<Statement>().unwrap()];

        assert_eq!(pattern.try_toplevel_match(&statements[0]), None);
    }

    #[test]
    fn agreeing_match() {
        let pattern = "p ^ p".parse::<PatternStatement>().unwrap();
        let statements = vec!["a ^ a".parse::<Statement>().unwrap()];

        let expected = Substitution::parse_owned("p: a").unwrap();

        let actual = pattern
            .try_toplevel_match(&statements[0])
            .as_ref()
            .map(Substitution::to_owned);

        assert_eq!(actual, Some(expected));
    }

    fn potential_set_test(patterns: &[&str], statements: &[&str], expected: &[&[(&str, &str)]]) {
        let patterns = patterns
            .iter()
            .map(|p| p.parse::<PatternStatement>().unwrap())
            .collect::<Vec<_>>();
        let statements = statements
            .iter()
            .map(|s| s.parse::<Statement>().unwrap())
            .collect::<Vec<_>>();

        let patterns = patterns.iter().collect();

        let potential_sets = PatternStatement::get_potential_sets(&patterns, &statements);

        let potential_owned = potential_sets
            .into_iter()
            .map(|set| {
                set.into_iter()
                    .map(|(p, s)| (p.to_owned(), statements[s.0].get_sub_path(&s.1).clone()))
                    .collect::<BTreeMap<PatternStatement, Statement>>()
            })
            .collect::<HashSet<_>>();

        let expected = expected
            .iter()
            .map(|set| {
                set.iter()
                    .map(|(p, s)| {
                        (
                            p.parse::<PatternStatement>().unwrap(),
                            s.parse::<Statement>().unwrap(),
                        )
                    })
                    .collect()
            })
            .collect();

        assert_eq!(potential_owned, expected);
    }

    #[test]
    fn pair_potential_sets() {
        potential_set_test(&["p"], &["a"], &[&[("p", "a")]])
    }

    #[test]
    fn substatement_potential_sets() {
        potential_set_test(
            &["p", "q"],
            &["a ^ b"],
            &[&[("p", "a"), ("q", "b")], &[("p", "b"), ("q", "a")]],
        )
    }

    fn match_test<'a, 'b, T: Into<Option<Vec<(&'a str, &'b str)>>>>(
        pattern: &str,
        statement: &str,
        expected: T,
    ) {
        let pattern = PatternStatement::new(pattern.parse::<Statement>().unwrap()).unwrap();
        let statements = vec![statement.parse::<Statement>().unwrap()];

        let expected = expected.into().map(|expected| {
            expected
                .into_iter()
                .map(|(l, r)| (Variable(String::from(l)), r.parse::<Statement>().unwrap()))
                .collect::<HashMap<_, _>>()
        });

        let matched = pattern
            .try_toplevel_match(&statements[0])
            .as_ref()
            .map(Substitution::to_owned);

        if matched != expected {
            if let Some(expected) = expected {
                eprintln!("Expected:");
                for (v, s) in expected.iter() {
                    eprintln!("{}: {}", v.0, s);
                }
            } else {
                eprintln!("Expected None");
            }

            if let Some(matched) = matched {
                eprintln!("Actual:");
                for (v, s) in matched.iter() {
                    eprintln!("{}: {}", v.0, s);
                }
            } else {
                eprintln!("Actual None");
            }

            panic!();
        }
    }

    #[test]
    fn unary_match_test() {
        match_test("!p", "![a -> b]", vec![("p", "a -> b")])
    }

    #[test]
    fn binary_match_test() {
        match_test("p -> q", "[a ^ b] -> a", vec![("p", "a ^ b"), ("q", "a")]);
    }

    #[test]
    fn match_conflict_test() {
        match_test("p -> p", "a -> b", None)
    }

    #[test]
    fn substitute_single() {
        let temp1 = Variable("p".to_string());

        let statements = vec!["a ^ b".parse::<Statement>().unwrap()];

        let pattern = "p".parse::<Statement>().unwrap();
        let matches =
            Substitution(once((&temp1, statements[0].clone())).collect::<HashMap<_, _>>());

        let expected = Statement::Binary(Box::new(BinaryExpression {
            lhs: Statement::Variable(Variable("a".to_string())),
            rhs: Statement::Variable(Variable("b".to_string())),
            op: BinaryOp::Conjunction,
        }));

        assert_eq!(matches.apply(&pattern), expected);
    }
}
