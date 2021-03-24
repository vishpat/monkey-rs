use crate::object::Object;

pub fn get_inbuilt_function(identifier: &str) -> Option<Object> {
    match identifier {
        "len" => Some(Object::FunctionInBuilt(String::from("len"))),
        _ => None
    }
}

fn process_len_function(params: &Vec<Object>) -> Object {

    if params.len() != 1 {
        panic!("Expected a single argument to the len function found {} arguments",
               params.len())
    }
    let argument = &params[0];

    match argument {
        Object::String(s) => Object::Integer(s.len() as i64),
        _ => panic!("len expects a string argument")
    }
}

pub fn eval_inbuilt_function(func_obj: &Object, params: &Vec<Object>) -> Object {
    match func_obj {
        Object::FunctionInBuilt(func_name) => {
            match func_name.as_str() {
                "len" => {
                    return process_len_function(params)
                }
                _ => panic!("Invalid inbuild function {}", func_name),
            }
        }
        _ => panic!("Excepted a function object but found {}", func_obj)
    }
    Object::Nil
}
