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
    let (mut p, c) = argument::parse_prolog(s)?;
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

/*fn max_place(num: usize) -> usize {
    if num == 0 {
        return 0;
    }

    let mut sum = 0;

    let mut fact = 1;
    for i in 1.. {
        fact *= i;
        sum += i * fact;
        if sum >= num {
            return i;
        }
    }

    unreachable!()
}

fn factorial(num: usize) -> usize {
    if num == 0 {
        1
    } else {
        (1..=num).product()
    }
}

fn as_factoradic(num: usize) -> Vec<usize> {
    let mut result = Vec::new();

    for place in (0..=max_place(num)).rev() {
        let place_value = factorial(place);

        result.push(num / place_value);

        num %= place_value;
    }

    result
}*/

#[cfg(test)]
mod tests {
    use super::*;

    #[ignore]
    #[test]
    fn two_rules() {
        assert_eq!(
            Ok(Some(true)),
            prove("b :- a -> b, a ^ b")
        );
    }

    #[ignore]
    #[test]
    fn nested_rule() {
        assert_eq!(
            Ok(None),
            prove("a -> c :- [a ^ !b] -> c"),
        );
    }
}
