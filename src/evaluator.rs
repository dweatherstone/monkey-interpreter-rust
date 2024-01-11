use crate::{
    ast::{BlockStatement, ExpressionNode, IfExpression, Program, StatementNode},
    object::Object,
};

const TRUE: Object = Object::Boolean(true);
const FALSE: Object = Object::Boolean(false);
const NULL: Object = Object::Null;

pub struct Evaluator {}

impl Evaluator {
    pub fn new() -> Self {
        Evaluator {}
    }

    pub fn eval_program(&self, program: Program) -> Object {
        let mut result = Object::Null;
        for stmt in program.statements {
            result = self.eval_statement(stmt);

            if let Object::ReturnValue(ret) = result {
                return *ret;
            }
        }

        result
    }

    fn eval_statement(&self, stmt: StatementNode) -> Object {
        match stmt {
            StatementNode::Expression(exp_stmt) => self.eval_expression(exp_stmt.expression),
            StatementNode::Return(ret_stmt) => {
                let value = self.eval_expression(ret_stmt.ret_value);
                Object::ReturnValue(Box::new(value))
            }
            _ => NULL,
        }
    }

    fn eval_expression(&self, expression: Option<ExpressionNode>) -> Object {
        if let Some(exp) = expression {
            return match exp {
                ExpressionNode::Integer(int_lit) => Object::Integer(int_lit.value),
                ExpressionNode::BooleanNode(bool_exp) => {
                    Self::native_bool_to_boolean_object(bool_exp.value)
                }
                ExpressionNode::Prefix(prefix_exp) => {
                    let right = self.eval_expression(Some(*prefix_exp.right));
                    Self::eval_prefix_expression(prefix_exp.operator, right)
                }
                ExpressionNode::Infix(infix_exp) => {
                    let left = self.eval_expression(Some(*infix_exp.left));
                    let right = self.eval_expression(Some(*infix_exp.right));
                    Self::eval_infix_expression(infix_exp.operator, &left, &right)
                }
                ExpressionNode::IfExpressionNode(if_exp) => self.eval_if_expression(if_exp),
                _ => NULL,
            };
        }
        NULL
    }

    fn eval_prefix_expression(op: String, right: Object) -> Object {
        match op.as_str() {
            "!" => Self::eval_bang_operator_expression(right),
            "-" => Self::eval_minus_prefix_operator_expression(right),
            _ => NULL,
        }
    }

    fn eval_infix_expression(op: String, left: &Object, right: &Object) -> Object {
        match (left, right, op) {
            // 5 == 10, 5 != 10, 5 < 10, 5 > 10 etc.
            (Object::Integer(left), Object::Integer(right), op) => {
                Self::eval_integer_infix_expression(op, *left, *right)
            }
            // true == true, (5 < 10) == true, etc.
            (Object::Boolean(left), Object::Boolean(right), op) => match op.as_str() {
                "==" => Self::native_bool_to_boolean_object(left == right),
                "!=" => Self::native_bool_to_boolean_object(left != right),
                _ => NULL,
            },
            _ => NULL,
        }
    }

    fn eval_if_expression(&self, exp: IfExpression) -> Object {
        let condition = self.eval_expression(Some(*exp.condition));
        if Self::is_truthy(condition) {
            self.eval_block_statement(exp.consequence)
        } else if let Some(alt) = exp.alternative {
            self.eval_block_statement(alt)
        } else {
            NULL
        }
    }

    fn is_truthy(obj: Object) -> bool {
        match obj {
            Object::Null => false,
            Object::Boolean(true) => true,
            Object::Boolean(false) => false,
            _ => true,
        }
    }

    fn eval_block_statement(&self, block: BlockStatement) -> Object {
        let mut result = NULL;

        for stmt in block.statements {
            result = self.eval_statement(stmt);

            if result.object_type() == "RETURN_VALUE" {
                return result;
            }
        }
        result
    }

    fn eval_bang_operator_expression(right: Object) -> Object {
        match right {
            Object::Boolean(true) => FALSE,
            Object::Boolean(false) => TRUE,
            Object::Null => TRUE,
            _ => FALSE,
        }
    }

    fn eval_minus_prefix_operator_expression(right: Object) -> Object {
        match right {
            Object::Integer(int_value) => Object::Integer(-int_value),
            _ => NULL,
        }
    }

    fn eval_integer_infix_expression(op: String, left: i64, right: i64) -> Object {
        match op.as_str() {
            "+" => Object::Integer(left + right),
            "-" => Object::Integer(left - right),
            "*" => Object::Integer(left * right),
            "/" => Object::Integer(left / right),
            "==" => Self::native_bool_to_boolean_object(left == right),
            "!=" => Self::native_bool_to_boolean_object(left != right),
            "<" => Self::native_bool_to_boolean_object(left < right),
            ">" => Self::native_bool_to_boolean_object(left > right),
            _ => NULL,
        }
    }

    fn native_bool_to_boolean_object(boolean: bool) -> Object {
        if boolean {
            TRUE
        } else {
            FALSE
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{lexer::Lexer, object::Object, parser::Parser};

    use super::Evaluator;

    #[test]
    fn test_eval_integer_expression() {
        let tests = vec![
            ("5", 5),
            ("10", 10),
            ("-5", -5),
            ("-10", -10),
            ("--5", 5),
            ("5 + 5 + 5 + 5 - 10", 10),
            ("2 * 2 * 2 * 2 * 2", 32),
            ("-50 + 100 + -50", 0),
            ("5 * 2 + 10", 20),
            ("5 + 2 * 10", 25),
            ("20 + 2 * -10", 0),
            ("50 / 2 * 2 + 10", 60),
            ("2 * (5 + 10)", 30),
            ("3 * 3 * 3 + 10", 37),
            ("3 * (3 * 3) + 10", 37),
            ("(5 + 10 * 2 + 15 / 3) * 2 + -10", 50),
        ];
        for test in tests {
            let evaluated = test_eval(test.0);
            test_integer_object(evaluated, test.1);
        }
    }

    #[test]
    fn test_eval_boolean_expression() {
        let tests = vec![
            ("true", true),
            ("false", false),
            ("1 < 2", true),
            ("1 > 2", false),
            ("1 > 1", false),
            ("1 == 1", true),
            ("1 == 2", false),
            ("1 != 1", false),
            ("1 != 2", true),
            ("1 == -1", false),
            ("1 != -1", true),
            ("1 < -1", false),
            ("1 > -1", true),
            ("true == true", true),
            ("false == false", true),
            ("true == false", false),
            ("true != false", true),
            ("false != true", true),
            ("(1 < 2) == true", true),
            ("(1 < 2) == false", false),
            ("(1 > 2) == true", false),
            ("(1 > 2) == false", true),
        ];
        for test in tests {
            let evaluated = test_eval(test.0);
            test_boolean_object(evaluated, test.1);
        }
    }

    #[test]
    fn test_eval_bang_operator() {
        let tests = vec![
            ("!true", false),
            ("!false", true),
            ("!5", false),
            ("!!true", true),
            ("!!false", false),
            ("!!5", true),
        ];
        for test in tests {
            let evaluated = test_eval(test.0);
            test_boolean_object(evaluated, test.1);
        }
    }

    #[test]
    fn test_if_else_expression() {
        let tests = vec![
            ("if (true) { 10 }", 10),
            ("if (false) { 10 }", -999),
            ("if (1) { 10 }", 10),
            ("if (1 < 2) { 10 }", 10),
            ("if (1 > 2) { 10 }", -999),
            ("if (1 > 2) { 10 } else { 20 }", 20),
            ("if (1 < 2) { 10 } else { 20 }", 10),
        ];
        for test in tests {
            let evaluated = test_eval(test.0);
            if test.1 == -999 {
                test_null_object(evaluated);
            } else {
                test_integer_object(evaluated, test.1)
            }
        }
    }

    #[test]
    fn test_return_statements() {
        let tests = vec![
            ("return 10;", 10),
            ("return 10; 9;", 10),
            ("return 2 * 5; 9;", 10),
            ("9; return 2 * 5; 9;", 10),
            (
                "if (10 > 1) {
                if (10 > 1) {
                    return 10;
                }
                return 1;
            }",
                10,
            ),
        ];
        for test in tests {
            let evaluated = test_eval(test.0);
            test_integer_object(evaluated, test.1);
        }
    }

    fn test_eval(input: &str) -> Object {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        let evaluator = Evaluator::new();
        evaluator.eval_program(program.unwrap())
    }

    fn test_integer_object(obj: Object, expected: i64) {
        match obj {
            Object::Integer(int_value) => assert_eq!(
                int_value, expected,
                "object has wrong value. Got = {}, want = {}",
                int_value, expected
            ),
            other => panic!("object is not integer. Got = {:?}", other),
        }
    }

    fn test_boolean_object(obj: Object, expected: bool) {
        match obj {
            Object::Boolean(bool_value) => assert_eq!(
                bool_value, expected,
                "object has wrong value. Got = {}, want = {}",
                bool_value, expected
            ),
            other => panic!("object is not bool. Got = {:?}", other),
        }
    }

    fn test_null_object(obj: Object) {
        // match obj {
        //     Object::Null => assert!(true),
        //     _ => assert!(false),
        // }
        assert!(obj.object_type() == *"NULL");
    }
}
