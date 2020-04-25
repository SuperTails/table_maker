// TODO: Remove
#![allow(dead_code)]

pub mod argument;
mod parse;
pub mod statement;
pub mod substitution;

/// Convenience function to turn a bool into a 'T' or 'F'
pub fn get_letter(value: bool) -> char {
    if value {
        'T'
    } else {
        'F'
    }
}

/// Convenience function to parse and prove an arugment
pub fn prove(s: &str) -> Result<Option<bool>, String> {
    let (mut p, c) = argument::parse_writeup(s)?;
    let result = argument::prove_validity(&mut p, &c);
    println!("---");
    for r in p.iter() {
        println!("{}", r);
    }
    println!("---");
    Ok(result)
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Variable(pub String);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    #[ignore]
    fn two_rules() {
        assert_eq!(
            Ok(Some(true)),
            prove(
                r#"
            a -> b
            a ^ b
            ---
            b
        "#
            )
        );
    }

    #[test]
    #[ignore]
    fn nested_rule() {
        assert_eq!(
            Ok(Some(true)),
            prove(
                r#"
            [a ^ !b] -> c
            ---
            c -> a
        "#
            )
        );
    }
}
