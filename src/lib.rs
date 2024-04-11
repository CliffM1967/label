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

use std::cell::RefCell;
use std::collections::HashMap;
use std::io::{stderr, stdout, Write};
use std::mem::replace;
use std::rc::Rc;

#[derive(Debug, PartialEq)]
pub enum Token {
    String(String),
    Symbol(String),
}

#[derive(Debug, PartialEq)]
enum Command {
    Symbol(String),
    String(String),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StackEntry {
    String(String),
    Environment(SharedEnvironment),
}

#[derive(Debug, Clone, PartialEq)]
struct Environment {
    map: HashMap<String, SharedStackEntry>,
    parent: Option<Box<SharedEnvironment>>,
}

type SharedStackEntry = Rc<RefCell<StackEntry>>;
type SharedEnvironment = Rc<RefCell<Environment>>;
type Stack = Vec<SharedStackEntry>;

impl Environment {
    fn new() -> Self {
        let m = HashMap::new();
        Self {
            map: m,
            parent: None,
        }
    }

    fn new_shared() -> SharedEnvironment {
        Rc::new(RefCell::new(Self::new()))
    }

    fn child_get(&self) -> SharedEnvironment {
        let mut new_env = Self::new_shared();
        let parent = self.clone(); 
        let parent = Rc::new(RefCell::new(parent));
        new_env.borrow_mut().assign_parent(parent);
        new_env
    }

    fn parent_get(&self) -> Result<SharedEnvironment, String> {
        if self.parent.is_none() {
            return Err("Cannot get parent environment".to_string());
        }
        let parent = self.parent.clone().unwrap();
        Ok(*parent)
    }

    fn assign_parent(&mut self, parent: SharedEnvironment) {
        self.parent = Some(Box::new(parent.clone()));
    }

    fn define(&mut self, key: String, value: SharedStackEntry) {
        self.map.insert(key, value);
    }

    // how deeply nested is this environment ?
    fn depth(&self) -> u64 {
        if self.parent.is_none() {
            return 1;
        }
        (self.parent.as_ref().unwrap()).borrow().depth() + 1
    }

    fn lookup(&self, key: String) -> Result<SharedStackEntry, String> {
        // look locally and return if found
        if self.map.contains_key(&key) {
            return Ok(self.map.get(&key).unwrap().clone());
        }
        if self.parent.is_none() {
            return Err(format!("Cannot lookup '{key}'"));
        }
        // we have a parent, so recursively call lookup there
        (self.parent.as_ref().unwrap()).borrow().lookup(key)
    }

    fn contains(&self, key: String) -> bool {
        self.lookup(key).is_ok()
    }
}


fn print_stderr(s: &str) {
    eprintln!("{s}");
    let _ = stderr().flush();
}


// convert an Option into a result with a given error string
fn option_to_result<T>(option: Option<T>, message: &str) -> Result<T, String> {
    match option {
        None => Err(message.to_string()),
        Some(x) => Ok(x),
    }
}

impl StackEntry {
    fn get_string(&self) -> String {
        match self {
            Self::String(s) => s.to_string(),
            _ => panic!("pop expected string"),
        }
    }

    fn get_env(&self) -> SharedEnvironment {
        match self {
            Self::Environment(e) => e.clone(),
            _ => panic!("pop expected environment"),
        }
    }
}

fn stack_pop(stack: &mut Stack) -> Result<SharedStackEntry, String> {
    let sse = stack.pop();
    match sse {
        Some(sse) => Ok(sse),
        _ => Err("Couldn't pop stack".to_string()),
    }
}


fn stack_pop_string(stack: &mut Stack, message: &str) -> Result<String, String> {
    let sse = stack.pop();
    if sse.is_none() {
        return Err("pop on Empty stack:Expected test name".to_string());
    }
    let sse = sse.unwrap();
    let se = sse.borrow();
    let s = se.get_string();
    Ok(s)
}

fn stack_pop_env(stack: &mut Stack, message: &str) -> Result<Rc<RefCell<Environment>>, String> {
    let sse = stack.pop();
    if sse.is_none() {
        return Err("pop on Empty stack:Expected environment".to_string());
    }
    let sse = sse.unwrap();
    let se = sse.borrow();
    let e = se.get_env();
    Ok(e)
}

fn _prelude() -> String {
    "".to_string()
}

fn prelude() -> String {
    std::fs::read_to_string("prelude.label").unwrap()
}

// Some tests run with an empty prelude
fn run(program: &str) -> Result<Stack, String> {
    run_with_passed_prelude(program, "".to_string())
}

// what we run in main.rs
pub fn run_with_prelude(program: &str) -> Result<Stack, String> {
    run_with_passed_prelude(program, prelude())
}

fn make_sse(se: StackEntry) -> SharedStackEntry {
    Rc::new(RefCell::new(se))
}

fn make_sses(s: String) -> SharedStackEntry {
    make_sse(StackEntry::String(s))
}

fn get_env(se: SharedStackEntry) -> SharedEnvironment {
    let se = (*se).borrow_mut();
    match &*se {
        StackEntry::Environment(e) => e.clone(),
        _ => panic!("cannot get environment"),
    }
}

// both of the above call this function
fn run_with_passed_prelude(program: &str, prelude: String) -> Result<Stack, String> {
    // prefix the prelude with a space
    let program = format!("{} {}", prelude, program);
    let mut program = parse(&program)?;
    // going to be popping the commands off, so reverse the parse() result
    program.reverse();

    let mut stack = vec![];

    // initialise our environment for DEFINE and LOOKUP
    let mut env = Environment::new_shared();

    loop {
        if program.len() == 0 {
            return Ok(stack);
        }
        let cmd = program.pop().unwrap();
        //println!("{:?} ",cmd);
        match cmd {
            Command::String(s) => stack.push(make_sses(s)),
            Command::Symbol(s) => match s.as_str() {
                "DUP" => run_dup(&mut stack)?,
                "DEFINE" => env = run_define(env,&mut stack)?, 
                "LOOKUP" => run_lookup(&env,&mut stack)?,
                "EXECUTE" => {
                    let subprogram = stack_pop_string(&mut stack, "no string for EXECUTE")?;
                    let mut cmds = parse(&subprogram)?;
                    program.push(Command::Symbol("LEAVE".to_string()));
                    cmds.reverse();
                    program.extend(cmds);
                    program.push(Command::Symbol("ENTER".to_string()));
                    program.push(Command::Symbol("CREATE".to_string()));
                }
                "CREATE" => {
                    let se = StackEntry::Environment(Environment::new_shared());
                    stack.push(make_sse(se));
                }

                "ENTER" => {
                    let se = get_env(stack.pop().unwrap());
                    //  want se.parent to be env
                    se.clone().borrow_mut().assign_parent(env.clone());
                    env = se; 
                }
                "LEAVE" => {
                    let e;
                    {
                        e = env.borrow().parent_get()?
                    };
                    env = e;
                }

                "xCHILD" => env = env.clone().borrow().child_get(),
                "xPARENT" => env = env.clone().borrow().parent_get()?,

                "ERROR" => match stack.len() {
                    0 => return Err("ERROR TERMINATION:Empty Stack".to_string()),
                    _ => {
                        let text = stack_pop_string(&mut stack, "foo")?;
                        let r = format!("ERROR TERMINATION:{text}");
                        return Err(r);
                    }
                },

                "STEQ" => {
                    //  pop all 4 arguments off the stack
                    let unequal_string = stack_pop_string(&mut stack, "STEQ:no string")?;
                    let equal_string = stack_pop_string(&mut stack, "STEQ:no string")?;
                    let s1 = stack_pop_string(&mut stack, "STEQ:no string")?;
                    let s2 = stack_pop_string(&mut stack, "STEQ:no string")?;
                    if s1 == s2 {
                        stack.push(make_sses(equal_string));
                    } else {
                        stack.push(make_sses(unequal_string));
                    }
                }
                "JOIN" => {
                    let s1 = stack_pop_string(&mut stack, "JOIN:no string")?;
                    let s2 = stack_pop_string(&mut stack, "JOIN:no string")?;
                    stack.push(make_sses(s2 + &s1));
                }
                "CHOP" => {
                    let s1 = &stack_pop_string(&mut stack, "CHOP:no string")?;
                    let l = s1.len();
                    if l == 0 {
                        stack.push(make_sses("CHOP on empty string".to_string()));
                        program.push(Command::Symbol("ERROR".to_string()));
                    } else {
                        let chopped = (s1[..l - 1]).to_string();
                        let final_char = (s1[l - 1..]).to_string();
                        stack.push(make_sses(chopped));
                        stack.push(make_sses(final_char));
                    }
                }
                "TEST" => {
                    if stack.len() == 0 {
                        return Err("TEST on empty stack".to_string());
                    }
                    let boolean = stack_pop_string(
                        &mut stack,
                        "Expected boolean",)?;
                    let test_name = stack_pop_string(&mut stack, "Expected test name")?; 
                    if boolean != "true" {
                        // our TEST failed: report whole of stack
                        return Err(format!("TEST '{test_name}' failed on false {:?}", stack));
                    }
                    if stack.len() > 0 {
                        let additional = stack.pop().unwrap();
                        return Err(format!(
                            "TEST '{test_name}' failed with extra stack
                            entry '{:?}'",
                            additional
                        ));
                    }
                    // TEST passed so now just continue...
                }
                // s is a Symbol, so auto-execute if it's defined
                _ => {
                    let def = env.borrow().lookup(s)?;
                    let c = Command::String(def.borrow().get_string());
                    program.push(Command::Symbol("EXECUTE".to_string()));
                    program.push(c);
                    
                },
            },
        };
    }
}

fn run_dup(stack:&mut Stack)->Result<(),String>{
    let tos1 = stack.pop();
    if tos1.is_none() {
        return Err("Empty".to_string());
    };
    let tos1 = tos1.unwrap();
    let tos2 = tos1.clone();
    stack.push(tos1.clone());
    stack.push(tos2.clone());
    Ok(())
}

fn run_define(env:SharedEnvironment,stack:&mut Stack)
    ->Result<SharedEnvironment,String>{

    let key = stack_pop_string(stack, "no key for DEFINE")?;
    let value = stack.pop().unwrap();
    env.borrow_mut().define(key, value);
    Ok(env)
}

fn run_lookup(env:&SharedEnvironment,stack:&mut Stack)->Result<(),String>{
    let key = stack_pop_string(stack, "no key for LOOKUP")?;
    let value = env.borrow().lookup(key)?;
    stack.push(value);
    Ok(())
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
    fn test_run_dup() {
        let p1 = "[abc]DUP";
        let p2 = "[abc][abc]";
        assert_eq(p1, p2);
    }

    #[test]
    fn test_dup_empty_stack_error() {
        let result = run("DUP");
        assert!(result.is_err());
    }

    #[test]
    fn test_define_lookup() {
        // define the symbol 'a' and then look it up twice
        let p1 = "[foo][a]DEFINE [a]LOOKUP [a]LOOKUP";
        let p2 = "[foo][foo]";
        assert_eq(p1, p2);
    }

    #[test]
    fn test_execute() {
        // put a string on the stack, and then execute it...
        let p1 = "[[a] [b]]EXECUTE";
        let p2 = "[a][b]"; 
        assert_eq(p1, p2);
    }

    fn assert_eq(p1: &str, p2: &str) {
        let r1 = run(p1);
        let r2 = run(p2);
        assert_eq!(r1, r2);
    }

    fn assert_eq_prelude(p1: &str, p2: &str) {
        let r1 = run_with_prelude(p1);
        let r2 = run_with_prelude(p2);
        assert_eq!(r1, r2);
    }

    #[test]
    fn test_auto_execute() {
        let p1 = "[[a]][foo]DEFINE foo";
        let p2 = "[a]";
        assert_eq(p1, p2);
    }

    #[test]
    fn test_environment_new() {
        let e = Environment::new();
        assert!(e.parent.is_none());
    }

    #[test]
    fn test_child_scope() {
        // re-define foo in an inner environment.
        // after the EXECUTE we should recover the outer definition
        let p1 = "[[b]][foo]DEFINE [[a][foo]DEFINE]EXECUTE foo";
        let p2 = "[b]";
        assert_eq(p1, p2);
    }

    #[test]
    fn test_a_definition_for_dup() {
        let p1 = "[[temp]DEFINE [temp]LOOKUP [temp]LOOKUP][dup]DEFINE [a]dup";
        let p2 = "[a][a]";
        assert_eq(p1, p2);
    }

    #[test]
    fn test_drop() {
        let p1 = "[[temp]DEFINE][drop]DEFINE [a]drop";
        let p2 = "";
        assert_eq(p1, p2);
    }

    #[test]
    fn test_swap() {
        let p1 = "[[a]DEFINE [b]DEFINE [a]LOOKUP  [b]LOOKUP]
                  [swap]DEFINE 
                  [1][2]swap";

        let p2 = "[2][1]";
        assert_eq(p1, p2);
    }

    #[test]
    fn test_error_empty_stack() {
        let p = "ERROR";
        let r = run(p);
        match r {
            Err(s) => assert_eq!(s, "ERROR TERMINATION:Empty Stack"),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_error_message() {
        let p = "[xyz]ERROR";
        let r = run(p);
        match r {
            Err(s) => assert_eq!(s, "ERROR TERMINATION:xyz"),
            _ => assert!(false),
        }
    }

    #[test]
    fn test_stack_equality() {
        let p = "[a][a][equal][not equal]STEQ";
        assert_eq(p, "[equal]");

        let p = "[a][b][equal][not equal]STEQ";
        assert_eq(p, "[not equal]");
    }

    #[test]
    fn test_prelude_runs_and_returns_empty_stack() {
        // run empty program which will be prefixed with prelude
        let r = run_with_prelude("");
        match r {
            Err(ref e) => {
                println!("Prelude failed with {e}");
                assert!(false);
            }
            Ok(r) => assert_eq!(r.len(), 0),
        }
    }


    #[test]
    // the TEST primitive.
    // the stack looks like [XXX][T] or [XXX][F] where XXX is the
    // test-name.
    // There are 5 cases to consider.
    fn test_test() {
        // TEST on an stack with 0 or 1 entries is an error.
        // The 0 argument case:
        match run("TEST") {
            Err(s) => assert_eq!(s, "TEST on empty stack"),
            _ => assert!(false),
        }
        // The 1 argument case:
        match run("[x]TEST") {
            Err(s) => assert_eq!(s, "pop on Empty stack:Expected test name"),
            _ => assert!(false),
        }

        // TEST with [XXX][false] as TOS is a TEST failure
        match run("[XXX][false] TEST") {
            //Err(s) => assert_eq!(s, "TEST 'XXX' failed on false"),
            Err(s) => {
                println!("s is {s}");
                assert!(s.starts_with("TEST 'XXX' failed on false"))
            }
            _ => assert!(false),
        }

        // TEST with [XXX]true as TOS-1,TOS is only good if they
        // were the  only stack entries

        // this is the passing case. We expect no error, and just to
        // pass...
        match run("[XXX][true] TEST") {
            Err(_) => panic!("TEST failed but should have passed"),
            _ => (),
        }
    }

    #[test]
    // define foo, and then bar (to call foo)
    // calling bar should now be the same as foo
    fn test_symbol_aliasing() {
        let p = "[[a]][foo]DEFINE [foo][bar]DEFINE bar";
        assert_eq(p, "[a]");
    }

    #[test]
    fn test_join() {
        let p = "[abc][def]JOIN";
        assert_eq(p, "[abcdef]");
    }

    #[test]
    fn test_chop() {
        let p = "[abc]CHOP";
        assert_eq(p, "[ab][c]");
    }

    #[test]
    fn test_chop_empty_string() {
        match run("[]CHOP") {
            Err(t) => assert_eq!(t, "ERROR TERMINATION:CHOP on empty string"),
            _ => panic!("Should never get here"),
        }
    }

    #[test]
    fn test_create() {
        let r = run("CREATE");
        let se = StackEntry::Environment(Environment::new_shared());
        let sse = make_sse(se);
        assert_eq!(r.unwrap(), vec![sse]);
    }

    #[test]
    fn test_create_enter_leave() {
        let p1 = "[[a]][foo]: CREATE ENTER [b][foo]: LEAVE foo";
        let p2 = "[a]";
        assert_eq_prelude(p1, p2);
    }

    #[test]
    fn test_environments_clone_properly() {
        let p1 = "CREATE [e]: [e]? ENTER [[a]][foo]: LEAVE [e]?ENTER foo";
        let p2 = "[a]";
        assert_eq_prelude(p1, p2);
    }

    #[test]
    fn test_environments_clone_properly2() {
        let p1 = "CREATE dup ENTER [[a]][foo]: LEAVE ENTER foo";
        let p2 = "[a]";
        assert_eq_prelude(p1, p2);
    }

    #[test]
    fn test_environment_usage(){
        let p1 = "CREATE [e]: e [[bar]][foo]: LEAVE e foo";
        let p2 = "[[bar]]";
        assert_eq_prelude(p1,p2);
    }
}
