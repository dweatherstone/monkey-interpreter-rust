use crate::object::Object;

pub struct Builtins;

impl Builtins {
    pub fn all_builtins(&self) -> Vec<(String, Object)> {
        vec![(String::from("len"), Object::Builtin(b_len))]
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
        other => Object::Error(format!(
            "argument to 'len' not supported. Got {}",
            other.object_type()
        )),
    }
}
