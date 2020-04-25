use crate::Variable;
use crate::parse::ParseNode;
pub use crate::parse::BinaryOp;

#[derive(Debug, PartialEq, Eq)]
pub enum SimpleStatement {
    Variable(Variable),
    Negation(Box<SimpleStatement>),
    BinaryOperation{ lhs: Box<SimpleStatement>, rhs: Box<SimpleStatement>, op: BinaryOp },
}

impl From<ParseNode<'_>> for SimpleStatement {
    fn from(node: ParseNode<'_>) -> Self {
        match node {
            ParseNode::Variable(v) => SimpleStatement::Variable(Variable(v.into())),
            ParseNode::Negation(p) => SimpleStatement::Negation(Box::new((*p).into())),
            ParseNode::BinaryOperation{ lhs, rhs, op } => {
                SimpleStatement::BinaryOperation{
                    lhs: Box::new((*lhs).into()),
                    rhs: Box::new((*rhs).into()),
                    op
                }
            }
        }
    }
}