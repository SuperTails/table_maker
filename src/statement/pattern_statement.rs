use super::{Statement, StatementPath, pathed_substs, UnaryExpression, BinaryExpression};
use crate::substitution::Substitution;
use crate::parse::ParseNode;
use std::collections::{HashSet, HashMap, BTreeMap};
use std::iter::once;
use std::str::FromStr;
use std::convert::TryFrom;
use std::ops::Deref;
use std::fmt;

macro_rules! maybe_match {
    ($p:path = $e:expr) => {
        if let $p(inner) = $e {
            Some(inner)
        } else {
            None
        }
    };
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

    /*
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
    ) -> Vec<PatternSetMatch<'a>> {
        // Each pattern must appear exactly once,
        // which means that we must have enough
        // statements to match against
        if statements.len() < patterns.len() {
            return Vec::new();
        }

        Self::get_potential_sets(&patterns, &statements)
            .into_iter()
            .filter_map(|potential| {
                let (patterns, images): (Vec<_>, Vec<_>) = potential.into_iter().map(|(p, s)| (p.clone(), s)).unzip();
                PatternSetMatch::new(statements, &patterns, images)
             })
            .collect()
    }
    */

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

impl fmt::Display for PatternStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Pattern: {{ {} }}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Variable;

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
}