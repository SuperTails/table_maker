use crate::statement::{BinaryExpression, Statement, UnaryExpression};
use crate::Variable;
use std::collections::{hash_map, HashMap, HashSet};
use std::fmt;

pub type SubstitutionIter<'c, 'a> = hash_map::Iter<'c, &'a Variable, Statement>;

#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct Substitution<'a>(pub HashMap<&'a Variable, Statement>);

impl<'a> Substitution<'a> {
    pub fn new() -> Substitution<'a> {
        Substitution(HashMap::new())
    }

    /// Creates a new statement by replacing variables in the given statement
    /// with the corresponding entry in this substitution
    pub fn apply(&self, statement: &Statement) -> Statement {
        let bound = statement.bound_variables().collect::<HashSet<_>>();
        for new_bound in self.0.keys() {
            // Ensure we can't double-bind variables
            assert!(!bound.contains(new_bound));
        }

        match statement {
            Statement::Variable(v) => self.0.get(v).unwrap_or(statement).clone(),
            Statement::Binary(b) => Statement::Binary(Box::new(BinaryExpression {
                lhs: self.apply(&b.lhs),
                rhs: self.apply(&b.rhs),
                op: b.op,
            })),
            Statement::Unary(u) => Statement::Unary(Box::new(UnaryExpression {
                inner: self.apply(&u.inner),
                op: u.op,
            })),
            _ => todo!(),
        }
    }

    pub fn iter<'c>(&'c self) -> SubstitutionIter<'c, 'a> {
        self.0.iter()
    }

    /// Convenience method for calling `try_insert` on every member of another `Substitution`
    #[must_use]
    pub fn try_merge(mut self, other: &Substitution<'a>) -> Option<Substitution<'a>> {
        for n in other.iter() {
            self.try_insert(n.0, n.1.clone())?;
        }
        Some(self)
    }

    /// Adds the given variable to statement substitution pair if it does not
    /// contradict the existing substitutions
    #[must_use]
    pub fn try_insert(&mut self, v: &'a Variable, s: Statement) -> Option<()> {
        // TODO: Better (i.e. non-structural) equality.
        // That would also require a variable mapping to multiple statements,
        // which I don't feel like supporting yet.
        if let Some(matched) = self.0.get(v) {
            if *matched != s {
                return None;
            }
        // Otherwise we would add the other statement
        // to the same variable
        } else {
            self.0.insert(v, s);
        }

        Some(())
    }

    pub fn to_owned(&self) -> HashMap<Variable, Statement> {
        self.iter()
            .map(|(k, v)| ((*k).clone(), (*v).clone()))
            .collect()
    }

    pub fn parse_owned(s: &str) -> Result<HashMap<Variable, Statement>, String> {
        s.lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .map(|line| {
                let mut parts = line.split(':');
                let variable = parts
                    .next()
                    .ok_or_else(|| "Expected variable".to_string())?
                    .trim();
                let statement = parts
                    .next()
                    .ok_or_else(|| "Expected statement".to_string())?
                    .trim();

                if parts.next().is_some() {
                    return Err("Unexpected ':' in line".to_string());
                }

                Ok((
                    Variable(variable.to_string()),
                    statement.parse::<Statement>()?,
                ))
            })
            .collect()
    }
}

impl fmt::Display for Substitution<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            write!(f, "Empty Substitution Set")
        } else {
            // TODO: Print variables properly
            for (idx, sub) in self.iter().enumerate() {
                write!(f, "{:?} -> {:?}", sub.0, sub.1)?;

                if idx + 1 != self.0.len() {
                    writeln!(f)?;
                }
            }

            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::BinaryOp;
    use std::iter::once;

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
