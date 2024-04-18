use label::{run_with_prelude, stack_to_string};
use std::process::exit;

fn main() {
    let program = std::env::args().nth(1);
    if program.is_none() {
        println!("Error");
        println!("Usage label \"XXX\" where XXX is your program");
        exit(1);
    } else {
        // first check the prelude runs to completion
        match run_with_prelude("") {
            Ok(_) => (),
            Err(e) => {
                println!("There was a problem with the prelude {e}");
                exit(1);
            }
        }
        // now run the program as requested
        let result = run_with_prelude(&program.unwrap());
        match result {
            Ok(stack) => println!("{}", stack_to_string(stack)),
            Err(e) => println!("ERROR:{e}"),
        }
    }
}
