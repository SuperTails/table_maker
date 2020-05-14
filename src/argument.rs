use crate::statement::{PatternStatement, Statement, FuncApplication, PatternSetMatch, all_injections, StatementPath, NEGATION};
use lazy_static::lazy_static;
use std::str::FromStr;

/// Determines if the given predicates imply the conclusion
///
/// Returns `Some(true)` if they do, `Some(false)` if they imply
/// the inverse of the conclusion, or `None` if the solver
/// could not determine an answer either way
pub fn prove_validity(predicates: &mut Vec<Statement>, conclusion: &Statement) -> Option<bool> {
    let not = Statement::FuncApplication(FuncApplication::unary(
        conclusion.clone(),
        &*NEGATION,
    ));

    let mut last_len = None;
    
    while last_len != Some(predicates.len()) {
        last_len = Some(predicates.len());

        for (argument, _name) in ARGUMENTS.iter() {
            let new = argument.apply(&predicates);
            for n in new {
                if !predicates.contains(&n) {
                    predicates.push(n);
                }
            }
        }

        if predicates.contains(&conclusion) {
            return Some(true);
        }

        if predicates.contains(&not) {
            return Some(false);
        }

    }

    None
}

#[derive(Debug, Clone, PartialEq)]
pub struct Argument {
    predicates: Vec<PatternStatement>,
    conclusion: Statement,
}

impl Argument {
    pub fn predicates(&self) -> &[PatternStatement] {
        &self.predicates
    }

    pub fn conclusion(&self) -> &Statement {
        &self.conclusion
    }

    //-- General form of this algorithm --
    //  Let P be the set of pattern statements in this argument
    //  Let Q be the conclusion of this argument
    //  Let I be a set of input statements, for example: { a, (a -> b) -> c }
    //  For every input statement J in I,
    //      Let J' be its complement I\J
    //      For every substatement S in J,
    //          Let the context C be the set (S union J')
    //          For every `PatternSetMatch` M between P and C,
    //              Substitute between Q(M) and S to get a new result statement
    //
    // To substitute:
    //  Replace S with this argument's conclusion and then `apply()` the substitution

    // TODO: Maybe just rewrite this as an iterator because that's really all it is
    pub fn algo(&self, input: &[Statement]) -> Vec<Statement> {
        let mut result = Vec::new();

        // P is `self.predicates()`
        // Q is `self.conclusion()`
        // I is `input`

        // For every input statement J in I ...
        for (sub_idx, j) in input.iter().enumerate() {
            // Let J' be its complement I\J
            let complement = input.iter().enumerate().filter_map(|(idx, i)| if i != j { Some((i.clone(), idx, StatementPath::new())) } else { None }).collect::<Vec<_>>();

            // For every substatement S in J ...
            for ((sub, sub_path), _) in j.substatements() {
                // Let the context C be the set (S union J')
                let mut context = complement.clone();
                context.push((sub.clone(), sub_idx, sub_path.clone()));

                for index_set in all_injections(self.predicates().len(), context.len()) {
                    let images = index_set.into_iter().map(|idx| (context[idx].1, context[idx].2.clone())).collect::<Vec<_>>();

                    if let Some(psm) = PatternSetMatch::new(input, self.predicates(), images) {
                        let new_s = psm.substitution().apply(self.conclusion());

                        let mut s = j.clone();
                        *s.sub_path_mut(&sub_path) = new_s;

                        if !result.contains(&s) {
                            result.push(s);
                        }
                    }
                }
            }
        }

        result
    }

    /// Returns a vec of the statements that can be inferred from the input
    /// using this argument
    pub fn apply(&self, statements: &[Statement]) -> Vec<Statement> {
        self.algo(statements)
    }
}

pub fn parse_prolog(s: &str) -> Result<(Vec<Statement>, Statement), String> {
    let (head, body) = {
        let mut n = s.trim().split(":-");
        let head = n
            .next()
            .ok_or_else(|| "Could not find head".to_string())?;
        let body = n
            .next()
            .ok_or_else(|| "Could not find body".to_string())?;

        if n.next() != None {
            return Err("Too many instances of ':-' in string".to_string());
        }
        (head, body)
    };

    // TODO: This will go very badly if I ever allow commas in statements
    let head = head.parse::<Statement>()?;
    let body = body
        .split(',')
        .map(|s| s.parse::<Statement>())
        .collect::<Result<Vec<Statement>, String>>()?;

    Ok((body, head))
}

pub fn parse_writeup(s: &str) -> Result<(Vec<Statement>, Statement), String> {
    let (predicates, conclusion) = {
        let mut n = s.trim().split("---\n");
        let p = n
            .next()
            .ok_or_else(|| "Could not find predicates".to_string())?;
        let c = n
            .next()
            .ok_or_else(|| "Could not find conclusion".to_string())?;

        if n.next() != None {
            return Err("Too many instances of '---' in string".to_string());
        }
        (p, c)
    };

    let conclusion = conclusion.parse::<Statement>()?;
    let predicates = predicates
        .split('\n')
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.parse::<Statement>())
        .collect::<Result<Vec<Statement>, String>>()?;

    Ok((predicates, conclusion))
}

impl FromStr for Argument {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (predicates, conclusion) = parse_writeup(s)?;
        let predicates = predicates
            .into_iter()
            .map(|s| {
                PatternStatement::new(s)
                    .ok_or_else(|| "Failed to create pattern statement".to_string())
            })
            .collect::<Result<_, String>>()?;

        Ok(Argument {
            predicates,
            conclusion,
        })
    }
}

macro_rules! argument_list {
    ($(pub static ref $name:ident: Argument = create_argument($data:literal);)*) => {
        /// A listing module for all of the constants representing argument forms
        pub mod argument_forms {
            use super::Argument;
            use lazy_static::lazy_static;
            lazy_static! {
                $(
                    pub static ref $name: Argument = $data.parse().unwrap();
                )*
            }
        }

        lazy_static! {
            /// lazy_static representing all usable argument forms
            pub static ref ARGUMENTS: Vec<(&'static Argument, &'static str)> = vec![$((&argument_forms::$name, stringify!($name)),)*];
        }
    };
}

argument_list! {
    pub static ref MODUS_PONENS: Argument = create_argument(
        r#"
        p -> q
        p
        ---
        q
    "#
    );
    pub static ref MODUS_TOLLENS: Argument = create_argument(
        r#"
        p -> q
        !q
        ---
        !p
    "#
    );
    pub static ref HYPOTHETICAL_SYLLOGISM: Argument = create_argument(
        r#"
        p -> q
        q -> r
        ---
        p -> r
    "#
    );
    pub static ref DISJUNCTIVE_SYLLOGISM: Argument = create_argument(
        r#"
        p V q
        !p
        ---
        q
    "#
    );
    pub static ref SIMPLIFICATION: Argument = create_argument(
        r#"
        p ^ q
        ---
        p  
    "#
    );
    /* TODO:
    pub static ref CONJUNCTION: Argument = create_argument(
        r#"
        p
        q
        ---
        p ^ q
    "#
    );*/
    pub static ref RESOLUTION: Argument = create_argument(
        r#"
        p V q
        [!p] V r
        ---
        q V r
    "#
    );

    // TODO: THE FOLLOWING SHOULD BE EQUIVALENCES
    pub static ref IMPLICATION: Argument = create_argument(
        r#"
        p -> q
        ---
        [!p] V q
    "#
    );
    pub static ref DEMORGANS_1: Argument = create_argument(
        r#"
        ![p ^ q]
        ---
        [!p] V [!q]
    "#
    );
    pub static ref DOUBLE_INVERSION: Argument = create_argument(
        r#"
        ![!p]
        ---
        p
    "#
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inner_match_apply() {
        let statements = vec![
            "[a -> b] -> c".parse::<Statement>().unwrap(),
            "a".parse::<Statement>().unwrap(),
        ];

        let expected = vec!["b -> c".parse::<Statement>().unwrap()];
        let actual = argument_forms::MODUS_PONENS.apply(&statements);

        if expected != actual {
            eprintln!("Expected:");
            for e in expected.iter() {
                eprintln!("{}", e);
            }
            eprintln!("Actual:");
            for a in actual.iter() {
                eprintln!("{}", a);
            }
        }

        assert_eq!(expected, actual);
    }
}
