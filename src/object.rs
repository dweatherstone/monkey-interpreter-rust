use std::{collections::HashMap, fmt::Display};

use crate::{
    ast::{BlockStatement, Identifier, Node},
    builtins::Builtins,
};

pub type BuiltinFunction = fn(Vec<Object>) -> Object;

#[derive(Debug, Clone)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    ReturnValue(Box<Object>),
    Error(String),
    Func(Function),
    StringObj(String),
    Builtin(BuiltinFunction),
    Array(Vec<Object>),
    Null,
}

impl Object {
    pub fn object_type(&self) -> String {
        match self {
            Self::Integer(_) => String::from("INTEGER"),
            Self::Boolean(_) => String::from("BOOLEAN"),
            Self::ReturnValue(_) => String::from("RETURN_VALUE"),
            Self::Error(_) => String::from("ERROR"),
            Self::Func(_) => String::from("FUNCTION"),
            Self::StringObj(_) => String::from("STRING"),
            Self::Builtin(_) => String::from("BUILTIN"),
            Self::Array(_) => String::from("ARRAY"),
            Self::Null => String::from("NULL"),
        }
    }
}

impl Display for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(int_value) => write!(f, "{}", int_value),
            Self::Boolean(bool_value) => write!(f, "{}", bool_value),
            Self::ReturnValue(ret_val) => write!(f, "{}", *ret_val),
            Self::Error(err) => write!(f, "ERROR: {}", err),
            Self::Func(function) => {
                let mut out = String::from("");
                let mut params = Vec::new();
                for p in &function.parameters {
                    params.push(p.print_string());
                }
                out.push_str("fn(");
                out.push_str(params.join(", ").as_str());
                out.push_str(") {\n");
                out.push_str(function.body.print_string().as_str());
                out.push_str("\n}");

                write!(f, "{}", out)
            }
            Self::StringObj(string) => write!(f, "{}", string),
            Self::Builtin(_) => write!(f, "builtin function"),
            Self::Array(arr) => {
                let mut out = String::from("");
                let mut elements = Vec::new();
                for el in arr {
                    elements.push(format!("{}", el));
                }

                out.push('[');
                out.push_str(elements.join(", ").as_str());
                out.push(']');
                write!(f, "{}", out)
            }
            Self::Null => write!(f, "null"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Environment {
    pub store: HashMap<String, Object>,
    pub outer: Option<Box<Environment>>,
}

impl Environment {
    pub fn new_environment() -> Environment {
        let mut env_map = HashMap::new();
        Self::init_builtins(&mut env_map);
        Environment {
            store: env_map,
            outer: None,
        }
    }

    pub fn new_enclosed_environment(outer: Box<Environment>) -> Environment {
        let mut env_map = HashMap::new();
        Self::init_builtins(&mut env_map);
        Environment {
            store: env_map,
            outer: Some(outer),
        }
    }

    fn init_builtins(hashmap: &mut HashMap<String, Object>) {
        let builtin_functions = Builtins;
        let builtins = builtin_functions.all_builtins();
        for (name, object) in builtins {
            hashmap.insert(name, object);
        }
    }

    pub fn get(&self, name: String) -> Option<Object> {
        match self.store.get(&name) {
            Some(obj) => Some(obj.clone()),
            None => match &self.outer {
                Some(outer_env) => outer_env.get(name),
                None => None,
            },
        }
    }

    pub fn set(&mut self, name: String, value: Object) -> Option<Object> {
        self.store.insert(name.clone(), value);
        self.get(name)
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub parameters: Vec<Identifier>,
    pub body: BlockStatement,
    pub env: Environment,
}
