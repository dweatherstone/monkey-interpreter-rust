use crate::{
    ast::{Identifier, LetStatement, Program, ReturnStatement, StatementNode},
    lexer::Lexer,
    token::{Token, TokenKind},
};

pub struct Parser {
    lexer: Lexer,
    cur_token: Token,
    peek_token: Token,
    errors: Vec<String>,
}

impl Parser {
    pub fn new(lexer: Lexer) -> Parser {
        let mut parser = Parser {
            lexer,
            cur_token: Default::default(),
            peek_token: Default::default(),
            errors: Vec::new(),
        };
        parser.next_token();
        parser.next_token();
        parser
    }

    fn next_token(&mut self) {
        self.cur_token = self.peek_token.clone();
        self.peek_token = self.lexer.next_token();
    }

    pub fn parse_program(&mut self) -> Option<Program> {
        let mut program = Program {
            statements: Vec::new(),
        };

        while !self.cur_token_is(TokenKind::Eof) {
            if let Some(statement) = self.parse_statement() {
                program.statements.push(statement);
            }
            self.next_token();
        }

        Some(program)
    }

    fn parse_statement(&mut self) -> Option<StatementNode> {
        match self.cur_token.kind {
            TokenKind::Let => self.parse_let_statement(),
            TokenKind::Return => self.parse_return_statement(),
            _ => None,
        }
    }

    #[allow(clippy::needless_return)]
    fn parse_let_statement(&mut self) -> Option<StatementNode> {
        let mut stmt = LetStatement {
            token: self.cur_token.clone(),
            name: Default::default(),
            value: Default::default(),
        };

        return if !self.expect_peek(TokenKind::Ident) {
            None
        } else {
            stmt.name = Identifier {
                token: self.cur_token.clone(),
                value: self.cur_token.literal.clone(),
            };

            if !self.expect_peek(TokenKind::Assign) {
                None
            } else {
                self.next_token();
                // TODO: Parse the expression
                while !self.cur_token_is(TokenKind::Semicolon) {
                    self.next_token();
                }
                Some(StatementNode::Let(stmt))
            }
        };
    }

    fn parse_return_statement(&mut self) -> Option<StatementNode> {
        let stmt = ReturnStatement {
            token: self.cur_token.clone(),
            ret_value: Default::default(),
        };
        self.next_token();
        while !self.cur_token_is(TokenKind::Semicolon) {
            self.next_token();
        }
        Some(StatementNode::Return(stmt))
    }

    fn expect_peek(&mut self, expected: TokenKind) -> bool {
        if self.peek_token_is(expected.clone()) {
            self.next_token();
            return true;
        }
        self.peek_error(expected);
        false
    }

    fn peek_token_is(&self, expected: TokenKind) -> bool {
        self.peek_token.kind == expected
    }

    fn cur_token_is(&self, expected: TokenKind) -> bool {
        self.cur_token.kind == expected
    }

    fn errors(&self) -> &Vec<String> {
        &self.errors
    }

    fn peek_error(&mut self, expected: TokenKind) {
        let msg = format!(
            "expected next token to be {}, got {} instead",
            expected, self.peek_token.kind
        );
        self.errors.push(msg);
    }
}

#[cfg(test)]
mod test {
    use crate::{
        ast::{Node, StatementNode},
        lexer::Lexer,
    };

    use super::Parser;

    #[test]
    fn test_let_statements() {
        let input = r#"
        let x = 5;
        let y= 10;
        let foobar = 838383;
        "#;

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        check_parser_errors(parser);
        match program {
            Some(program) => {
                assert_eq!(
                    program.statements.len(),
                    3,
                    "statements does not contain 3 statements. Got={}",
                    program.statements.len()
                );
                let expected = vec!["x", "y", "foobar"];

                for (idx, exp) in expected.into_iter().enumerate() {
                    let stmt = &program.statements[idx];
                    test_let_statement(stmt, exp);
                }
            }
            None => panic!("parse program should not be None"),
        };
    }

    #[test]
    fn test_invalid_let_statement() {
        let input = r#"
        let x 5;
        let y 10;
        let foobar = 838383;
        "#;

        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        match program {
            Some(program) => {
                // let foobar = 838383;
                assert_eq!(
                    program.statements.len(),
                    1,
                    "statements does not contain 1 statement. Got={}",
                    program.statements.len()
                );
                // let x 5;
                // let y 10;
                let expected_errors = vec![
                    String::from("expected next token to be =, got Int instead"),
                    String::from("expected next token to be =, got Int instead"),
                ];

                for (idx, exp) in expected_errors.into_iter().enumerate() {
                    let err = &parser.errors[idx];
                    assert_eq!(
                        err, &exp,
                        "Unexpected error message. Expected: '{}', got: '{}'",
                        exp, err
                    );
                }
            }
            None => panic!("parse program should not be None"),
        };
    }

    #[test]
    fn test_return_statement() {
        let input = r#"
        return 5;
        return 10;
        return add(5, 10);
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        match program {
            Some(program) => {
                assert_eq!(
                    program.statements.len(),
                    3,
                    "statements does not contain 3 statements. Got={}",
                    program.statements.len()
                );
                for stmt in program.statements {
                    match stmt {
                        StatementNode::Return(ret_stmt) => {
                            assert_eq!(
                                ret_stmt.token_literal(),
                                "return",
                                "token literal not 'return', got = {}",
                                ret_stmt.token_literal()
                            );
                        }
                        other => panic!("not a ReturnStatement, got {:?}", other),
                    };
                }
            }
            None => panic!("parse program should not be None"),
        };
    }

    fn test_let_statement(stmt: &StatementNode, expected: &str) {
        assert_eq!(
            stmt.token_literal(),
            "let",
            "token literal not 'let', got={}",
            stmt.token_literal()
        );
        match stmt {
            StatementNode::Let(let_stmt) => {
                assert_eq!(
                    let_stmt.name.value, expected,
                    "LetStatement name value not {}, got {}",
                    expected, let_stmt.name.value
                );
                assert_eq!(
                    let_stmt.name.token_literal(),
                    expected,
                    "LetStatement name value not {}, got {}",
                    expected,
                    let_stmt.name.token_literal()
                );
            }
            other => panic!("not a Let statement, got {:?}", other),
        }
    }

    fn check_parser_errors(parser: Parser) {
        let errors = parser.errors();

        if errors.is_empty() {
            return;
        }
        for error in errors {
            eprintln!("parser error: {}", error);
        }
        panic!("parser error present");
    }
}
