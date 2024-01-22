use crate::{evaluator::NULL, object::Object};

pub struct Builtins;

impl Builtins {
    pub fn all_builtins(&self) -> Vec<(String, Object)> {
        vec![
            (String::from("len"), Object::Builtin(b_len)),
            (String::from("first"), Object::Builtin(b_first)),
            (String::from("last"), Object::Builtin(b_last)),
            (String::from("rest"), Object::Builtin(b_rest)),
            (String::from("push"), Object::Builtin(b_push)),
        ]
    }
}

fn b_len(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        return Object::Error(format!(
            "wrong number of arguments. Got = {}, want = 1",
            args.len()
        ));
    }
    match &args[0] {
        Object::StringObj(str_lit) => Object::Integer(str_lit.len() as i64),
        Object::Array(elements) => Object::Integer(elements.len() as i64),
        other => Object::Error(format!(
            "argument to 'len' not supported. Got {}",
            other.object_type()
        )),
    }
}

fn b_first(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        return Object::Error(format!(
            "wrong number of arguments. Got = {}, want = 1",
            args.len()
        ));
    }
    match &args[0] {
        Object::Array(elements) => {
            if elements.is_empty() {
                NULL
            } else {
                elements[0].clone()
            }
        }
        other => Object::Error(format!(
            "argument to 'first' not supported. Got {}",
            other.object_type()
        )),
    }
}

fn b_last(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        return Object::Error(format!(
            "wrong number of arguments. Got = {}, want = 1",
            args.len()
        ));
    }
    match &args[0] {
        Object::Array(elements) => {
            if elements.is_empty() {
                NULL
            } else {
                elements[elements.len() - 1].clone()
            }
        }
        other => Object::Error(format!(
            "argument to 'last' not supported. Got {}",
            other.object_type()
        )),
    }
}

fn b_rest(args: Vec<Object>) -> Object {
    if args.len() != 1 {
        return Object::Error(format!(
            "wrong number of arguments. Got = {}, want = 1",
            args.len()
        ));
    }
    match &args[0] {
        Object::Array(elements) => {
            let length = elements.len();
            if length > 0 {
                let new_elements = elements[1..].to_vec();
                Object::Array(new_elements)
            } else {
                NULL
            }
        }
        other => Object::Error(format!(
            "argument to 'rest' not supported. Got {}",
            other.object_type()
        )),
    }
}

fn b_push(args: Vec<Object>) -> Object {
    if args.len() != 2 {
        return Object::Error(format!(
            "wrong number of arguments. Got = {}, want = 2",
            args.len()
        ));
    }
    match &args[0] {
        Object::Array(elements) => {
            let mut new_elements = elements.clone();
            new_elements.push(args[1].clone());
            Object::Array(new_elements)
        }
        other => Object::Error(format!(
            "argument to 'push' must be ARRAY. Got {}",
            other.object_type()
        )),
    }
}
