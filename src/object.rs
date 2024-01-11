use std::fmt::Display;

#[derive(Debug)]
pub enum Object {
    Integer(i64),
    Boolean(bool),
    ReturnValue(Box<Object>),
    Error(String),
    Null,
}

impl Object {
    pub fn object_type(&self) -> String {
        match self {
            Self::Integer(_) => String::from("INTEGER"),
            Self::Boolean(_) => String::from("BOOLEAN"),
            Self::ReturnValue(_) => String::from("RETURN_VALUE"),
            Self::Error(_) => String::from("ERROR"),
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
            Self::Null => write!(f, "null"),
        }
    }
}
