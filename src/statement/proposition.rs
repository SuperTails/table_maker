use super::Statement;
use crate::Variable;
use std::collections::{HashSet, HashMap};

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