use crate::token::Token;

pub trait Node {
    fn token_literal(&self) -> String;
    fn print_string(&self) -> String;
}

#[derive(Debug)]
pub enum StatementNode {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
}

impl Node for StatementNode {
    #[allow(clippy::needless_return)]
    fn token_literal(&self) -> String {
        return match self {
            Self::Let(let_stmt) => let_stmt.token_literal(),
            Self::Return(ret_stmt) => ret_stmt.token_literal(),
            Self::Expression(exp_stmt) => exp_stmt.token_literal(),
        };
    }

    #[allow(clippy::needless_return)]
    fn print_string(&self) -> String {
        return match self {
            Self::Let(let_stmt) => let_stmt.print_string(),
            Self::Return(ret_stmt) => ret_stmt.print_string(),
            Self::Expression(exp_stmt) => exp_stmt.print_string(),
        };
    }
}

#[derive(Debug)]
pub enum ExpressionNode {
    IdentifierNode(Identifier),
}

impl Node for ExpressionNode {
    #[allow(clippy::needless_return)]
    fn token_literal(&self) -> String {
        return match self {
            Self::IdentifierNode(identifier) => identifier.token_literal(),
        };
    }

    #[allow(clippy::needless_return)]
    fn print_string(&self) -> String {
        return match self {
            Self::IdentifierNode(identifier) => identifier.print_string(),
        };
    }
}

pub struct Program {
    pub statements: Vec<StatementNode>,
}

impl Node for Program {
    #[allow(clippy::needless_return)]
    fn token_literal(&self) -> String {
        return if !self.statements.is_empty() {
            match &self.statements[0] {
                StatementNode::Let(let_stmt) => let_stmt.token_literal(),
                StatementNode::Return(ret_stmt) => ret_stmt.token_literal(),
                StatementNode::Expression(exp_stmt) => exp_stmt.token_literal(),
            }
        } else {
            String::from("")
        };
    }

    fn print_string(&self) -> String {
        let mut out = String::from("");

        for stmt in self.statements.as_slice() {
            out.push_str(stmt.print_string().as_str());
        }
        out
    }
}

#[derive(Debug)]
pub struct LetStatement {
    pub token: Token,
    pub name: Identifier,
    pub value: Option<ExpressionNode>,
}

impl Node for LetStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }

    fn print_string(&self) -> String {
        let mut out = String::from("");
        out.push_str(self.token_literal().as_str());
        out.push(' ');
        out.push_str(self.name.print_string().as_str());
        out.push_str(" = ");
        if let Some(value) = &self.value {
            out.push_str(value.print_string().as_str());
        }
        out.push(';');
        out
    }
}

#[derive(Debug, Default)]
pub struct ReturnStatement {
    pub token: Token,
    pub ret_value: Option<ExpressionNode>,
}

impl Node for ReturnStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }

    fn print_string(&self) -> String {
        let mut out = String::from("");
        out.push_str(self.token_literal().as_str());
        out.push(' ');
        if let Some(value) = &self.ret_value {
            out.push_str(value.print_string().as_str());
        }
        out.push(';');
        out
    }
}

#[derive(Debug, Default)]
pub struct Identifier {
    pub token: Token,
    pub value: String,
}

impl Node for Identifier {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }

    fn print_string(&self) -> String {
        self.value.clone()
    }
}

#[derive(Debug, Default)]
pub struct ExpressionStatement {
    pub token: Token,
    pub expression: Option<ExpressionNode>,
}

impl Node for ExpressionStatement {
    fn token_literal(&self) -> String {
        self.token.literal.clone()
    }

    fn print_string(&self) -> String {
        if let Some(expression) = &self.expression {
            return expression.print_string();
        }
        String::from("")
    }
}

#[cfg(test)]
mod test {
    use crate::{
        ast::Node,
        token::{Token, TokenKind},
    };

    use super::{ExpressionNode, Identifier, LetStatement, Program, StatementNode};

    #[test]
    fn test_print_string() {
        let program = Program {
            statements: vec![StatementNode::Let(LetStatement {
                token: Token {
                    kind: TokenKind::Let,
                    literal: String::from("let"),
                },
                name: Identifier {
                    token: Token {
                        kind: TokenKind::Ident,
                        literal: String::from("myVar"),
                    },
                    value: String::from("myVar"),
                },
                value: Some(ExpressionNode::IdentifierNode(Identifier {
                    token: Token {
                        kind: TokenKind::Ident,
                        literal: String::from("anotherVar"),
                    },
                    value: String::from("anotherVar"),
                })),
            })],
        };

        assert_eq!(
            program.print_string(),
            String::from("let myVar = anotherVar;"),
            "print string wrong. Got = '{}'",
            program.print_string()
        );
    }
}
