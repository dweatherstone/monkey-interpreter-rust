//use std::{cell::RefCell, rc::Rc};

use std::ops::Deref;

use crate::{
    ast::{BlockStatement, ExpressionNode, Identifier, IfExpression, Program, StatementNode},
    object::{Environment, Function, Object},
};

const TRUE: Object = Object::Boolean(true);
const FALSE: Object = Object::Boolean(false);
const NULL: Object = Object::Null;

pub struct Evaluator {
    //env: Rc<RefCell<Environment>>,
    env: Environment,
}

impl Evaluator {
    pub fn new() -> Self {
        Evaluator {
            //env: Rc::new(RefCell::new(Environment::new_environment())),
            env: Environment::new_environment(),
        }
    }

    pub fn eval_program(&mut self, program: Program) -> Object {
        let mut result = Object::Null;
        for stmt in program.statements {
            result = self.eval_statement(stmt);

            if let Object::ReturnValue(ret) = result {
                return *ret;
            }

            if let Object::Error(_) = result {
                return result;
            }
        }

        result
    }

    fn eval_statement(&mut self, stmt: StatementNode) -> Object {
        match stmt {
            StatementNode::Expression(exp_stmt) => self.eval_expression(exp_stmt.expression),
            StatementNode::Return(ret_stmt) => {
                let value = self.eval_expression(ret_stmt.ret_value);
                if Self::is_error(&value) {
                    return value;
                }
                Object::ReturnValue(Box::new(value))
            }
            StatementNode::Let(let_stmt) => {
                let value = self.eval_expression(let_stmt.value);
                if Self::is_error(&value) {
                    return value;
                }
                self.env.set(let_stmt.name.value, value).unwrap()
            }
            _ => NULL,
        }
    }

    fn eval_expression(&mut self, expression: Option<ExpressionNode>) -> Object {
        if let Some(exp) = expression {
            return match exp {
                ExpressionNode::Integer(int_lit) => Object::Integer(int_lit.value),
                ExpressionNode::BooleanNode(bool_exp) => {
                    Self::native_bool_to_boolean_object(bool_exp.value)
                }
                ExpressionNode::Prefix(prefix_exp) => {
                    let right = self.eval_expression(Some(*prefix_exp.right));
                    if Self::is_error(&right) {
                        return right;
                    }
                    Self::eval_prefix_expression(prefix_exp.operator, right)
                }
                ExpressionNode::Infix(infix_exp) => {
                    let left = self.eval_expression(Some(*infix_exp.left));
                    if Self::is_error(&left) {
                        return left;
                    }
                    let right = self.eval_expression(Some(*infix_exp.right));
                    if Self::is_error(&right) {
                        return right;
                    }
                    Self::eval_infix_expression(infix_exp.operator, &left, &right)
                }
                ExpressionNode::IfExpressionNode(if_exp) => self.eval_if_expression(if_exp),
                ExpressionNode::IdentifierNode(ident) => self.eval_identifier(ident),
                ExpressionNode::Function(fn_lit) => Object::Func(Function {
                    parameters: fn_lit.parameters,
                    body: fn_lit.body,
                    env: self.env.clone(),
                }),
                ExpressionNode::Call(call_exp) => {
                    let function = self.eval_expression(Some(call_exp.function.deref().clone()));
                    if Self::is_error(&function) {
                        return function;
                    }
                    let args = self.eval_expressions(call_exp.arguments);
                    if args.len() == 1 && Self::is_error(&args[0]) {
                        return args[0].clone();
                    }

                    self.apply_function(function, args)
                }
                _ => NULL,
            };
        }
        NULL
    }

    fn apply_function(&mut self, func: Object, args: Vec<Object>) -> Object {
        match func {
            Object::Func(function) => {
                let old_env = self.env.clone();
                let extended_env = self.extend_function_env(function.clone(), args);
                self.env = extended_env;
                let evaluated = self.eval_block_statement(function.body);
                self.env = old_env;
                Self::unwrap_return_value(evaluated)
            }
            other => Object::Error(format!("not a function: {}", other.object_type())),
        }
    }

    fn extend_function_env(&self, func: Function, args: Vec<Object>) -> Environment {
        let mut env = Environment::new_enclosed_environment(Box::new(func.env));
        for (idx, param) in func.parameters.into_iter().enumerate() {
            env.set(param.value, args[idx].clone());
        }
        env
    }

    fn unwrap_return_value(obj: Object) -> Object {
        match obj {
            Object::ReturnValue(ret) => *ret,
            _ => obj,
        }
    }

    fn eval_expressions(&mut self, exps: Vec<ExpressionNode>) -> Vec<Object> {
        let mut result = Vec::new();
        for expression in exps {
            let evaluated = self.eval_expression(Some(expression));
            if Self::is_error(&evaluated) {
                return vec![evaluated];
            }
            result.push(evaluated);
        }
        result
    }

    fn eval_prefix_expression(op: String, right: Object) -> Object {
        match op.as_str() {
            "!" => Self::eval_bang_operator_expression(right),
            "-" => Self::eval_minus_prefix_operator_expression(right),
            _ => Object::Error(format!("unknown operator: {}{}", op, right.object_type())),
        }
    }

    fn eval_infix_expression(op: String, left: &Object, right: &Object) -> Object {
        if left.object_type() != right.object_type() {
            return Object::Error(format!(
                "type mismatch: {} {} {}",
                left.object_type(),
                op,
                right.object_type()
            ));
        }
        match (left, right, op) {
            // 5 == 10, 5 != 10, 5 < 10, 5 > 10 etc.
            (Object::Integer(left), Object::Integer(right), op) => {
                Self::eval_integer_infix_expression(op, *left, *right)
            }
            // true == true, (5 < 10) == true, etc.
            (Object::Boolean(left_bool), Object::Boolean(right_bool), op) => match op.as_str() {
                "==" => Self::native_bool_to_boolean_object(left_bool == right_bool),
                "!=" => Self::native_bool_to_boolean_object(left_bool != right_bool),
                _ => Object::Error(format!(
                    "unknown operator: {} {} {}",
                    left.object_type(),
                    op,
                    right.object_type()
                )),
            },
            (left, right, op) => Object::Error(format!(
                "unknown operator: {} {} {}",
                left.object_type(),
                op,
                right.object_type()
            )),
        }
    }

    fn eval_if_expression(&mut self, exp: IfExpression) -> Object {
        let condition = self.eval_expression(Some(*exp.condition));
        if Self::is_truthy(condition) {
            self.eval_block_statement(exp.consequence)
        } else if let Some(alt) = exp.alternative {
            self.eval_block_statement(alt)
        } else {
            NULL
        }
    }

    fn eval_identifier(&self, identifier: Identifier) -> Object {
        let value = self.env.get(identifier.value.clone());
        match value {
            Some(val) => val,
            None => Object::Error(format!("identifier not found: {}", identifier.value)),
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

    fn eval_block_statement(&mut self, block: BlockStatement) -> Object {
        let mut result = NULL;

        for stmt in block.statements {
            result = self.eval_statement(stmt);

            if result.object_type() == "RETURN_VALUE" || result.object_type() == "ERROR" {
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
            _ => Object::Error(format!("unknown operator: -{}", right.object_type())),
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

    fn is_error(obj: &Object) -> bool {
        obj.object_type() == "ERROR"
    }
}

#[cfg(test)]
mod test {
    use crate::{ast::Node, lexer::Lexer, object::Object, parser::Parser};

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
    fn test_bang_operator() {
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

    #[test]
    fn test_error_handling() {
        let tests = vec![
            ("5 + true;", "type mismatch: INTEGER + BOOLEAN"),
            ("5 + true; 5;", "type mismatch: INTEGER + BOOLEAN"),
            ("-true", "unknown operator: -BOOLEAN"),
            ("true + false;", "unknown operator: BOOLEAN + BOOLEAN"),
            ("5; true + false; 5", "unknown operator: BOOLEAN + BOOLEAN"),
            (
                "if (10 > 1) {true + false;}",
                "unknown operator: BOOLEAN + BOOLEAN",
            ),
            (
                "if (10 > 1) { 
                if (10 > 1) {
                    return true + false;
                }
                return 1;
            }",
                "unknown operator: BOOLEAN + BOOLEAN",
            ),
            ("foobar", "identifier not found: foobar"),
        ];
        for test in tests {
            let evaluated = test_eval(test.0);
            match evaluated {
                Object::Error(err) => assert_eq!(err, test.1),
                other => panic!("no error object returned. Got = {:?}", other),
            }
        }
    }

    #[test]
    fn test_let_statements() {
        let tests = vec![
            ("let a = 5; a;", 5),
            ("let a = 5 * 5; a;", 25),
            ("let a = 5; let b = a; b;", 5),
            ("let a = 5; let b = a; let c = a + b + 5; c;", 15),
        ];
        for test in tests {
            test_integer_object(test_eval(test.0), test.1);
        }
    }

    #[test]
    fn test_function_object() {
        let input = "fn(x) { x + 2; };";
        let evaluated = test_eval(input);

        match evaluated {
            Object::Func(function) => {
                assert_eq!(
                    function.parameters.len(),
                    1,
                    "function has wrong parameters length. Got = {}",
                    function.parameters.len()
                );
                assert_eq!(
                    function.parameters[0].print_string(),
                    "x",
                    "parameter is not 'x'. Got = {}",
                    function.parameters[0].print_string()
                );
                assert_eq!(
                    function.body.print_string(),
                    "(x + 2)",
                    "body is not 'x + 2'. Got = {}",
                    function.body.print_string()
                );
            }
            other => panic!("object is not Function. Got = {:?}", other),
        }
    }

    #[test]
    fn test_function_application() {
        let tests = vec![
            ("let identity = fn(x) { x; }; identity(5);", 5),
            ("let identity = fn(x) { return x; }; identity(5);", 5),
            ("let double = fn(x) { x * 2; }; double(5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5, 5);", 10),
            ("let add = fn(x, y) { x + y; }; add(5 + 5, add(5, 5));", 20),
            ("fn(x) { x; }(5);", 5),
        ];
        for test in tests {
            test_integer_object(test_eval(test.0), test.1);
        }
    }

    #[test]
    fn test_closures() {
        let input = r#"
        let newAdder = fn(x) {
            fn(y) { x + y };
        };
        let addTwo = newAdder(2);
        addTwo(2);
        "#;
        test_integer_object(test_eval(input), 4);
    }

    fn test_eval(input: &str) -> Object {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let program = parser.parse_program();
        let mut evaluator = Evaluator::new();
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