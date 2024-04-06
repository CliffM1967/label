use label::run;

fn main() {
    let prog = std::env::args().nth(1);
    if prog.is_none() {
        println!("Error");
        println!("Usage label \"XXX\" where XXX is your program");
    } else {
        println!("{:?}", run(&prog.unwrap()));
    }
}
