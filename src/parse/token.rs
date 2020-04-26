#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Token<'a> {
    Variable(&'a str),
    Conjunction,
    Disjunction,
    Negation,
    OpenBracket,
    CloseBracket,
    RightArrow,
    DoubleArrow,
}

pub fn tokenize(input: &str) -> Result<Vec<Token>, String> {
    let mut input_iter = input.char_indices().enumerate();
    let mut result = Vec::new();

    while let Some((idx, (byte, c))) = input_iter.next() {
        let follow = input.chars().nth(idx + 1);
        let follow2 = input.chars().nth(idx + 2);

        let next = match c {
            '^' => Some(Token::Conjunction),
            'V' | 'v' => Some(Token::Disjunction),
            '!' | '~' => Some(Token::Negation),
            '→' => Some(Token::RightArrow),
            '↔' => Some(Token::DoubleArrow),
            '[' => Some(Token::OpenBracket),
            ']' => Some(Token::CloseBracket),
            '-' if follow == Some('>') => {
                input_iter.next();
                Some(Token::RightArrow)
            }
            '<' if follow == Some('-') && follow2 == Some('>') => {
                input_iter.next();
                input_iter.next();
                Some(Token::DoubleArrow)
            }
            _ if c.is_alphabetic() => Some(Token::Variable(&input[byte..][..c.len_utf8()])),
            _ if c.is_whitespace() => None,
            _ => return Err(format!("Failed to lex character '{}'", c)),
        };

        if let Some(next) = next {
            result.push(next);
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_tokenize() {
        assert_eq!(tokenize("->"), Ok(vec![Token::RightArrow]));
        assert_eq!(tokenize("<->"), Ok(vec![Token::DoubleArrow]));
    }
}
