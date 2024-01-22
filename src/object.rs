use std::{
    collections::{hash_map::DefaultHasher, HashMap},
    fmt::Display,
    hash::{Hash, Hasher},
};

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
    HashObj(HashStruct),
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
            Self::HashObj(_) => String::from("HASH"),
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
            Self::HashObj(hash) => {
                let mut out = String::new();
                let mut pairs = Vec::new();
                for pair in hash.pairs.values() {
                    pairs.push(format!("{}: {}", pair.key, pair.value));
                }

                out.push('{');
                out.push_str(pairs.join(", ").as_str());
                out.push('}');
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

#[derive(Debug, PartialEq, Clone, Eq)]
pub struct HashKey {
    pub object_type: String,
    pub value: i64,
}

impl Hash for HashKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
        self.object_type.hash(state);
    }
}

pub trait Hashable {
    fn hash_key(&self) -> Result<HashKey, String>;
}

impl Hashable for Object {
    fn hash_key(&self) -> Result<HashKey, String> {
        match &self {
            Object::Boolean(bool) => {
                let value = if *bool { 1 } else { 0 };
                Ok(HashKey {
                    object_type: self.object_type(),
                    value,
                })
            }
            Object::Integer(int) => Ok(HashKey {
                object_type: self.object_type(),
                value: *int,
            }),
            Object::StringObj(string) => {
                let mut hasher = DefaultHasher::new();
                string.hash(&mut hasher);
                Ok(HashKey {
                    object_type: self.object_type(),
                    value: hasher.finish() as i64,
                })
            }
            other => Err(format!("unusable as HashKey: {}", other.object_type())),
        }
    }
}

#[derive(Debug, Clone)]
pub struct HashPair {
    pub key: Object,
    pub value: Object,
}

#[derive(Debug, Clone)]
pub struct HashStruct {
    pub pairs: HashMap<HashKey, HashPair>,
}

#[cfg(test)]
mod test {
    use super::{Hashable, Object};

    #[test]
    fn test_string_hash_key() {
        let hello1 = Object::StringObj(String::from("Hello World"));
        let hello2 = Object::StringObj(String::from("Hello World"));
        let some_other = Object::StringObj(String::from("Some Other"));

        assert_eq!(
            hello1.hash_key(),
            hello2.hash_key(),
            "string with same content have different hash keys"
        );
        assert_ne!(
            hello1.hash_key(),
            some_other.hash_key(),
            "strings with different content have same hash keys"
        );
    }
}
