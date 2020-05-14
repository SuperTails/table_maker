use super::{Statement, PatternStatement, StatementPath};
use crate::substitution::Substitution;
use std::collections::HashSet;

/// A "pattern set match" is an injective binary relation from
/// a set *P* of pattern statements to
/// a set *C* (also called the *context*) of normal statements,
/// in which every element (p, c) satisfies: p matches c,
/// and which can be collected into a substitution (TODO: define that formally)
#[derive(Debug, Clone, PartialEq)]
pub struct PatternSetMatch<'a> {
    // This field might not actually be necessary
    statements: &'a [Statement],

    patterns: &'a [PatternStatement],
    /// This is *always* the same length as `patterns`
    /// and each index of patterns corresponds to the same index in this field
    images: Vec<(usize, StatementPath)>,

    substitution: Substitution<'a>,
}

impl<'a> PatternSetMatch<'a> {
    pub fn new(statements: &'a [Statement], patterns: &'a [PatternStatement], images: Vec<(usize, StatementPath)>) -> Option<Self> {
        assert_eq!(images.len(), patterns.len());

        let substitution = patterns.iter().zip(images.iter())
                .try_fold(Substitution::new(), |overall, (p1, st_path)| {
                    let st = statements[st_path.0].get_sub_path(&st_path.1);

                    let matched = p1.try_toplevel_match(st)?;
                    overall.try_merge(&matched)
                })?;
        
        Some(PatternSetMatch {
            statements,
            patterns,
            images,
            substitution,
        })
    } 

    pub fn substitution(&self) -> Substitution<'a> {
        self.substitution.clone()
    }

    pub fn pairs<'b>(&'b self) -> impl Iterator<Item = (&'a PatternStatement, &'b (usize, StatementPath))> {
        self.patterns.iter().zip(self.images.iter())
    }
}

impl<'a> IntoIterator for PatternSetMatch<'a> {
    type Item = (&'a PatternStatement, (usize, StatementPath));
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.patterns.iter().zip(self.images.into_iter()).collect::<Vec<_>>().into_iter()
    }
}

pub fn all_pairs(pattern_count: usize, statements: &[Statement]) -> impl Iterator<Item = Vec<&Statement>> {
    all_injections(pattern_count, statements.len()).into_iter().map(move |indices| {
        indices.into_iter().map(|i| &statements[i]).collect()
    })
}

/// If the input set I is 0, 1, 2 .. `input - 1`, and the output set O is 0, 1, 2 .. `output - 1`,
/// then this returns the set of all injective functions from I to O
pub fn all_injections(input: usize, output: usize) -> Vec<Vec<usize>> {
    if input > output {
        Vec::new()
    } else {
        let mut result = Vec::new();
        let mut data = vec![0; input];
        all_injections_inner(&(0..output).collect(), &mut data, 0, &mut result);
        result
    }
}

fn all_injections_inner(available: &HashSet<usize>, data: &mut [usize], idx: usize, result: &mut Vec<Vec<usize>>) {
    if idx == data.len() {
        result.push(data.to_vec());
    } else {
        for next in available.iter() {
            let mut remaining = available.clone();
            remaining.remove(next);

            data[idx] = *next;

            all_injections_inner(&remaining, data, idx + 1, result);
        }
    }
}

// Returns the set of all injective functions from `patterns` (P) to `statements`:
//pub fn all_pairs<'a>(patterns: &'a [PatternStatement], statements: &'a [Statement]) -> HashSet<Vec<usize>> {

//}