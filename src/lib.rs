// LABEL language development.

/*
We propose an incredibly simple language that bootstraps itself as much
as possible.  This will keep the underlying implementation as simple as
possible, and hopefully expose as much of the evaluation/type system as
possible to the user.  The idea is to eschew any big up-front design
to avoid wasting time implementing features we might not need.

So we start by defining a program to be a simple ASCII string.
We will tokenise that into two different things, symbols, and strings.

The strings will be delimited by [] chars.
The symbols will be alphanumeric, and the underscore character.
Ignoring whitespace, anything else will be a single-char symbol.
*/

use std::io::{stderr, stdout, Write};
use std::collections::HashMap;

#[derive(Debug, PartialEq)]
pub enum Token {
    String(String),
    Symbol(String),
}

struct Environment{
    map : HashMap<String,String>,
    parent : Option<Box<Environment>>,
}

impl Environment{
    fn new()->Self{
        let m = HashMap::new();
        Self { map:m , parent:None }
    }

    fn child_get(self)->Environment{
        let mut new_env = Self::new();
        new_env.parent = Some(Box::new(self));
        new_env
    }

    fn parent_get(self)->Result<Environment,String>{
        if self.parent.is_none(){
            return Err("Cannot get parent environment".to_string());
        }
        Ok(*self.parent.unwrap())
    }

    fn define(&mut self,key:String,value:String){
        self.map.insert(key,value);
    }

    fn lookup(&self,key:String)->Result<String,String>{
        if self.map.contains_key(&key){
            return Ok(self.map.get(&key).unwrap().to_string());
        }
        if self.parent.is_none(){
            return Err(format!("Cannot lookup '{key}'"))
        }
        self.parent.as_ref().unwrap().lookup(key)
    }
}


/* The execution model is that Strings will be pushed onto a stack, while
commands will "execute" in some manner.

*/

/*
So the first order of business is going to be parsing a string into a
vector of tokens, so as can pop() them off in the order they are declared
*/

fn print_stderr(s: &str) {
    eprintln!("{s}");
    let _ = stderr().flush();
}

#[derive(Debug, PartialEq)]
enum Command {
    Symbol(String),
    String(String),
}


// convert an Option into a result with a given error string
fn option_to_result<T>(option:Option<T>,message:&str)->Result<T,String>{
    match option{
        None => Err(message.to_string()),
        Some(x) => Ok(x),
    }
}

fn stack_pop(stack:&mut Vec<String>,message:&str)->Result<String,String>{
    option_to_result(stack.pop(),message)
}

fn _prelude()->String{
    "".to_string()
}


fn prelude()->String{
    "
    [ Here is where we bootstrap our little language]
    [ It is clear that this is a comment, and it is polluting the stack]
    [ So the first thing to do is to define a word to drop the TOS]
    [ And then use that to clean up our comments]

    [[a]DEFINE][pop]DEFINE

    [ For brevity we define ';' to be pop ]
    [pop][;]DEFINE

    [ We now have 6 comment-strings on the stack, so drop them];;; ;;;
    [T]TEST   [ assert the stack is empty ];

    [ for brevity, we define ':' to be DEFINE ];
    [PARENT DEFINE CHILD][:]DEFINE  

    [ instead of writing [T]TEST we write assert_empty ];
    [[T]TEST][assert_empty]:

    [ we want [not] to negate [T] and [F] -- this we must take on trust ];
    [[T][F][T]STEQ][not]:

    assert_empty

    [F]not TEST  [ we can test [F]not but not [T]not ];
    [T]not not TEST [this is the best we can do!];


    [[T][F]STEQ][str_eq]:  [ defines string-equality ];
    [a][a]str_eq TEST
    [a][b]str_eq not TEST
    
    assert_empty


    [ 
      Now we an implement an IF command. It takes three arguments:
      a true_block, a false_block, and a boolean.
      Depending on the boolean, the corresponding block is executed.
    ];

    assert_empty
    ".to_string()
}

pub fn run(program: &str) -> Result<Vec<String>, String> {
    // prefix the prelude
    let program = format!("{} {}",prelude(),program);
    let mut program = parse(&program)?;
    // going to popping the commands off, so reverse the lex result
    program.reverse();

    let mut stack = vec![];
    
    // initialise our environment for DEFINE and LOOKUP
    let mut env = Environment::new();

    loop{
        //for cmd in parse(program)? {
        if program.len()==0 { return Ok(stack) }
        let cmd = program.pop().unwrap();    
        println!("Executing {:?}",cmd);
        match cmd {
            Command::String(s) => stack.push(s),
            Command::Symbol(s) => match s.as_str() {
                "DUP" => {
                    let tos = stack_pop(&mut stack,"Empty stack for DUP")?;
                    stack.push(tos.clone());
                    stack.push(tos);
                },
                "DEFINE" => {
                    let key = stack_pop(&mut stack,"no key for DEFINE")?;
                    let value = stack_pop(&mut stack,"no value for DEFINE")?;
                    env.define(key,value);
                },
                "LOOKUP" => {
                    let key = stack_pop(&mut stack,"no key for LOOKUP")?;
                    let value = env.lookup(key)?;
                    stack.push(value);
                },
                "EXECUTE" => {
                    let subprogram = stack_pop(&mut stack,"no string for EXECUTE")?;
                    let mut cmds = parse(&subprogram)?;
                    program.push(Command::Symbol("PARENT".to_string()));
                    cmds.reverse();
                    program.extend(cmds);
                    program.push(Command::Symbol("CHILD".to_string()));
                },
                "CHILD" => env = env.child_get(),
                "PARENT" => env = env.parent_get()?,
                "ERROR" => return Err("ERROR TERMINATION".to_string()),

                "STEQ" => {
                    //  pop all 4 arguments off the stack
                    let unequal_string = stack_pop(&mut stack,"STEQ:no string")?;
                    let equal_string = stack_pop(&mut stack,"STEQ:no string")?;
                    let s1 = stack_pop(&mut stack,"STEQ:no string")?;
                    let s2 = stack_pop(&mut stack,"STEQ:no string")?;
                    if s1==s2{
                        stack.push(equal_string);
                    } else {
                        stack.push(unequal_string);
                    }
                    
                },                
                "TEST" => {
                    if stack.len()==0 { 
                        return Err("TEST on empty stack".to_string()) 
                    }
                    let tos = stack.pop().unwrap();
                    if tos != "T"{
                        return Err("TEST failed on false".to_string());
                    }
                    if stack.len()>0{
                        return Err("TEST failed with stack entries".to_string());
                    }
                    // everything passed so now just continue...
                },
                
                _ => {
                    // if s exists as a string, fetch it and execute it
                    let s1 = s.clone();
                    let def = env.lookup(s)?;
                    let def1 = def.clone();
                    println!("Auto executing {s1} with definition {def1}");
                    program.push(Command::Symbol("EXECUTE".to_string()));
                    program.push(Command::String(def));
                }
            },
        }
    }
}

fn is_symbol_char(c: u8) -> bool {
    c.is_ascii_alphanumeric() || c == b'_'
}

fn convert_string(s: &[u8]) -> String {
    return std::str::from_utf8(s).unwrap().to_string();
}

fn lex(program: &str) -> Result<Vec<String>, String> {
    let mut ret = vec![];
    let bytes = program.as_bytes();
    let mut start = 0;
    let mut stop;
    loop {
        // search past leading whitespace
        while start < bytes.len() && bytes[start].is_ascii_whitespace() {
            start += 1
        }
        // if we have reached the end of the program, it's time to return
        if start == bytes.len() {
            return Ok(ret);
        }
        // if '[' we are at the start of a sub-string.
        if bytes[start] == b'[' {
            stop = start + 1;
            let mut depth = 1;
            while stop < bytes.len() && depth > 0 {
                if bytes[stop] == b'[' {
                    depth += 1
                }
                if bytes[stop] == b']' {
                    depth -= 1
                }
                stop += 1;
            }
            if depth > 0 {
                return Err(format!("Bad substring in lex:{program}"));
            }
            let substring = convert_string(&bytes[start..stop]);
            ret.push(substring);
            // stop is now past the ']' char
            start = stop;
            continue;
        }
        // we are at the start of something. are we a special single char?
        if !is_symbol_char(bytes[start]) {
            let symbol = convert_string(&bytes[start..start + 1]);
            ret.push(symbol);
            start += 1;
            continue;
        }
        // so we're at the start of a symbol.  Look for the end
        stop = start + 1;
        while stop < bytes.len() && is_symbol_char(bytes[stop]) {
            stop += 1
        }
        // extract the symbol and add it to the result
        let substring = convert_string(&bytes[start..stop]);
        ret.push(substring);
        // point start to next interesting byte
        start = stop;
    }
}

fn parse(program: &str) -> Result<Vec<Command>, String> {
    let mut cmds = vec![];
    let strings = lex(program);
    // extract the strings, or return the error from lex
    let strings = match strings {
        Err(s) => return Err(s),
        Ok(v) => v,
    };
    for s in strings {
        if s.starts_with("[") {
            // strip leading and trailing delimiters
            let ss = s[1..s.len() - 1].to_string();
            cmds.push(Command::String(ss));
        } else {
            cmds.push(Command::Symbol(s));
        }
    }
    Ok(cmds)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lex_empty_string() {
        let result: Vec<String> = lex("").unwrap();
        assert!(result.len() == 0)
    }

    #[test]
    fn test_lex_pure_whitespace() {
        let result = lex("   \n  \r").unwrap();
        assert!(result.len() == 0)
    }

    #[test]
    fn test_lex_single_symbol() {
        let result = lex("a");
        let expected = vec!["a".to_string()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_lex_multiple_symbols() {
        let result = lex(" ab c ");
        let expected = vec!["ab".to_string(), "c".to_string()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_lex_substring() {
        let result = lex("[hello world]");
        let expected = vec!["[hello world]".to_string()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_lex_nested_substring() {
        let result = lex("[a [b]]");
        let expected = vec!["[a [b]]".to_string()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_lex_single_char_symbol() {
        let result = lex("a:; = >a");
        let expected = vec![
            "a".to_string(),
            ":".to_string(),
            ";".to_string(),
            "=".to_string(),
            ">".to_string(),
            "a".to_string(),
        ];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_lex_error() {
        let result = lex("[ foo");
        match result {
            Ok(_) => (),
            Err(s) => assert_eq!(s, "Bad substring in lex:[ foo"),
        }
    }

    #[test]
    fn test_parse() {
        let result = parse("a [hello]");
        let expected = vec![
            Command::Symbol("a".to_string()),
            Command::String("hello".to_string()),
        ];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_run2() {
        let result = run("[abc][def]");
        let expected = vec!["abc".to_string(), "def".to_string()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_run_dup() {
        let result = run("[abc]DUP");
        let expected = vec!["abc".to_string(), "abc".to_string()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_dup_error() {
        let result = run("DUP");
        assert!(result.is_err());
    }

    #[test]
    fn test_define_lookup() {
        // define the symbol 'a' and then look it up twice
        let result = run("[foo][a]DEFINE [a]LOOKUP [a]LOOKUP");
        let expected = vec!["foo".to_string(), "foo".to_string()];
        assert_eq!(result, Ok(expected));
    }

    #[test]
    fn test_execute(){
        // put a string on the stack, and then execute it...
        let result = run("[[a] [b]]EXECUTE");
        let expected = vec!["a".to_string(),"b".to_string()];
        assert_eq!(result, Ok(expected));
    }

    fn assert_eq(p1:&str,p2:&str){
        let r1 = run(p1);
        let r2 = run(p2);
        assert_eq!(r1,r2);
    }

    #[test]
    fn test_auto_execute(){
        let p1 = "[[a]][foo]DEFINE foo";
        let p2 = "[a]";
        assert_eq(p1,p2);
    }


    #[test]
    fn test_environment_new(){
        let e = Environment::new();
        assert!(e.parent.is_none());
    }
    
    #[test]
    fn test_child_scope(){
        // re-define foo in an inner environment.
        // after the EXECUTE we should recover the outer definition
        let p1 = "[[b]][foo]DEFINE [[a][foo]DEFINE]EXECUTE foo";
        let p2 = "[b]";
        assert_eq(p1,p2); 
    }

    #[test]
    fn test_new_dup(){
        let p1 = "[[temp]DEFINE [temp]LOOKUP [temp]LOOKUP][dup]DEFINE [a]dup";
        let p2 = "[a][a]";
        assert_eq(p1,p2);
    }

    #[test]
    fn test_drop(){
        let p1 = "[[temp]DEFINE][drop]DEFINE [a]drop";
        let p2 = "";
        assert_eq(p1,p2);
    }

    #[test]
    fn test_swap(){
        let p1 = "[[a]DEFINE [b]DEFINE [a]LOOKUP  [b]LOOKUP]
                  [swap]DEFINE 
                  [1][2]swap";

        let p2 = "[2][1]";
        assert_eq(p1,p2);
    }

    #[test]
    fn test_error(){
        let p = "ERROR";
        let r = run(p);
        match r{
            Err(s) => assert_eq!(s,"ERROR TERMINATION"),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_stack_equality(){
        let p = "[a][a][equal][not equal]STEQ";
        assert_eq(p,"[equal]");

        let p = "[a][b][equal][not equal]STEQ";
        assert_eq(p,"[not equal]");
    }

    #[test]
    fn test_prelude_runs_and_returns_empty_stack(){
        // run empty program which will be prefixed with prelude
        let r = run("");
        // check it ran
        assert!(r.is_ok());
        // check it returned empty stack
        assert!(r.unwrap().len()==0);
    }

    #[test]
    fn test_string_equality(){
        let p = "[[T][F]STEQ][str_eq]DEFINE  [a][a]str_eq";
        assert_eq(p,"[T]");
        
        let p = "[[T][F]STEQ][str_eq]DEFINE  [a][b]str_eq";
        assert_eq(p,"[F]");
    }

    #[test]
    // the TEST primitive : single stack entry is [T]
    // there are 4 cases to consider.
    fn test_test(){
        // TEST on an empty stack is an error.
        match run("TEST"){
            Err(s) => assert_eq!(s,"TEST on empty stack"),
            _ => assert!(false),
        }

        // TEST with [F] as TOS is another error
        match run("[F]TEST"){
            Err(s) => assert_eq!(s,"TEST failed on false"),
            _ => assert!(false),
        }

        // TEST with [T] as TOS is only good if that was only stack entry
        match run("[T]TEST"){
            Ok(stack) => assert_eq!(stack.len(),0),
            _ => assert!(false),
        }

        match run("[a][T]TEST"){
            Err(s) => assert_eq!(s,"TEST failed with stack entries"),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_symbol_aliasing(){
        let p = "[[a]][foo]DEFINE [foo][bar]DEFINE bar";
        assert_eq(p,"[a]");
    }



    /*
        // an empty string should return an empty Vec<Token>.
        #[test]
        fn test_empty_string(){
            assert_eq!(parse("").len(),0);
        }

        // if all there is is whitespace, still going to get nothing back
        #[test]
        fn test_pure_whitespace(){
            assert_eq!(parse("     ").len(),0);
        }

        // single token
        #[test]
        fn test_single_token_symbol(){
            let r = parse("    a");
            assert_eq!(r,vec![Token::Symbol("a".to_string())]);
        }

        // single symbol can be alphanumeric + underscore
        #[test]
        fn test_single_command(){
        let r = parse("a_b");
        let t = vec![Token::Symbol("a_b".to_string())];
        assert_eq!(r,t);
        }

        #[test]
        fn test_multiple_symbols(){
            let r = parse("a bc d ");
            let t = vec![
                Token::Symbol("a".to_string()),
                Token::Symbol("bc".to_string()),
                Token::Symbol("d".to_string()),
                ];
           assert_eq!(r,t);
        }

        // strings are denoted  [XXX] where XXX is the string content
        #[test]
        fn test_single_empty_token_string(){
            let r = parse(" [] ");
            let t = vec![Token::String("".to_string())];
            assert_eq!(r,t);
        }

        #[test]
        fn test_single_token_string(){
            let r = parse(" [abc ]");
            let t = vec![Token::String("abc ".to_string())];
            assert_eq!(r,t);
        }

        // now strings can have strings inside them...
        #[test]
        fn test_recursive_string(){
            let r = parse(" [ [ab]] ");
            let t = vec![Token::String(" [ab]".to_string())];
            assert_eq!(r,t);
        }

        // we want any other non-whitespace chars to be single byte Symbols
        #[test]
        fn test_singe_byte_symbol(){
            let r = parse(":");
            let t = vec![Token::Symbol(":".to_string())];
            assert_eq!(r,t);
        }

        #[test]
        fn test_several_single_byte_symbol(){
            let r = parse(":;");
            let t = vec![
                Token::Symbol(":".to_string()),
                Token::Symbol(";".to_string())];
            assert_eq!(r,t);
        }


        #[test]
        fn test_trailing_single_byte_symbol(){
            let r = parse("a:");
            let t = vec![
                Token::Symbol("a".to_string()),
                Token::Symbol(":".to_string())];
            assert_eq!(r,t);
        }


        #[test]
        fn test_complex_example(){
            let r = parse("a bc d_e []:");
            let t = vec![
                Token::Symbol("a".to_string()),
                Token::Symbol("bc".to_string()),
                Token::Symbol("d_e".to_string()),
                Token::String("".to_string()),
                Token::Symbol(":".to_string()),
                ];
            assert_eq!(r,t);
        }

        #[test]
        fn test_empty_program(){
            let result:Vec<String> = run("");
            assert!(result.len()==0);
        }

        #[test]
        fn test_simple_program(){
            let result = run("[hello world!]");
            assert_eq!(result,vec!["hello world!"]);
        }
    */
}
