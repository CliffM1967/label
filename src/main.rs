use label::run_with_prelude;

fn main() {
    let prog = std::env::args().nth(1);
    if prog.is_none() {
        println!("Error");
        println!("Usage label \"XXX\" where XXX is your program");
    } else {
        println!("{:?}", run_with_prelude(&prog.unwrap()));
    }
}
