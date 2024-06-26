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

#[derive(Debug, PartialEq, Clone)]
enum Command {
    Symbol(String),
    String(String),
}

type Program = Vec<Command>;

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

    fn shared_equals2(e1: SharedEnvironment, e2: SharedEnvironment) -> bool {
        e1 == e2
    }

    // have to do this explicitly as using PartialOrd blows the stack
    // -- something to do with the Rc<RefCell<>> wrapper ?
    fn shared_equals(e1: SharedEnvironment, e2: SharedEnvironment) -> bool {
        print_stderr("shared_equals");
        let e1 = e1.borrow();
        let e2 = e2.borrow();
        let mut x = "foobar".to_string();
        if e1.depth() != e2.depth() {
            return false;
        }
        for e1k in e1.map.keys() {
            print_stderr(&format!("Checking e1 key {}", e1k));
            if !e2.map.contains_key(e1k) {
                return false;
            }
            match &*e1.map.get(e1k).unwrap().borrow() {
                StackEntry::String(s1) => {
                    let st = format!("comparing '{s1}'");
                    print_stderr(&st);
                    match &*e2.map.get(e1k).unwrap().borrow() {
                        StackEntry::String(s2) => {
                            x = s2.clone();
                            if s1 != s2 {
                                let st = format!("With {s2} failed");
                                print_stderr(&st);
                                return false;
                            }
                        }
                        StackEntry::Environment(se) => return false,
                    };
                    print_stderr(&format!("{}", *s1 == x));
                    print_stderr(&format!("'{s1}' was equal to '{x}'"));
                    print_stderr(&format!("{}", *s1 == x));
                    if *s1 != x {
                        print_stderr("returning false");
                        return false;
                    }
                }
                StackEntry::Environment(se) => {
                    match &*e2.map.get(e1k).unwrap().borrow() {
                        StackEntry::Environment(se2) => {
                            if !Environment::shared_equals(se.clone(),
                                se2.clone()){
                                return false  // don't return if true here
                                }
                        }
                        _ => return false,
                    };
                }
            };
        }
        print_stderr("other way around");
        for e2k in e2.map.keys() {
            if !e1.map.contains_key(e2k) {
                return false;
            }
            match &*e2.map.get(e2k).unwrap().borrow() {
                StackEntry::String(s1) => {
                    match &*e1.map.get(e2k).unwrap().borrow() {
                        StackEntry::String(s2) => {
                            let st=format!("Comparing '{s1}' with '{s2}'");
                            print_stderr(&st);
                            x = s2.clone();
                            if s1 != s2 {
                                print_stderr("returning false");
                                return false;
                            }
                        }
                        StackEntry::Environment(se) => return false,
                    };
                    if *s1 != x {
                        print_stderr("was not equal2");
                        return false;
                    }
                }
                StackEntry::Environment(se) => {
                    match &*e1.map.get(e2k).unwrap().borrow() {
                        StackEntry::Environment(se2) => {
                            if !Environment::shared_equals(se.clone(), se2.clone())
                            { return false // don't return true just yet!
                            }
                        }
                        _ => return false,
                    };
                }
            };
        }
        // check parents
        if e1.depth()>1{
            let st = format!("Checking parents depth {}",e1.depth());
            print_stderr(&st);
            let e1p = e1.parent_get().unwrap();
            let e2p = e2.parent_get().unwrap();
            if !Environment::shared_equals(e1p,e2p){
                return false
            }
        }
        print_stderr("Returning true");
        true
    }

    fn _to_string(&self) -> String {
        let mut r = vec![];
        r.push("<Env{".to_string());
        if self.map.contains_key("first") {
            let v = self.map.get("first").unwrap().borrow();
            match &*v {
                StackEntry::Environment(se) => {
                    let v = se.borrow();
                    if v.map.contains_key("second") {
                        let v = v.map.get("second").unwrap().borrow();
                        match &*v {
                            StackEntry::Environment(se) => {
                                let v = se.borrow();
                                if v.map.contains_key("first") {
                                    let v = v.map.get("first").unwrap().borrow();
                                    match &*v {
                                        StackEntry::String(s) => {
                                            r.push(format!("{}", s.to_string()))
                                        }
                                        _ => (),
                                    }
                                }
                            }
                            _ => (),
                        }
                    }
                }
                _ => (),
            }
        }
        r.push(" ".to_string());
        //for key in self.map.keys(){
        //    r.push(format!(".{key}. "));
        //}
        r.push("}".to_string());
        r.push(format!("{}", self.depth()));
        r.push(">".to_string());
        r.join("")
    }

    fn to_string(&self) -> String {
        let mut r = vec![];
        r.push("<Env{".to_string());
        r.push("}".to_string());
        r.push(format!("{}", self.depth()));
        r.push(">".to_string());
        r.join("")
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

// convert an Option<T> into a Result<T,String>  with a given error string
fn option_to_result<T>(option: Option<T>, message: &str) -> Result<T, String> {
    match option {
        None => Err(message.to_string()),
        Some(x) => Ok(x),
    }
}

impl StackEntry {
    fn to_string(&self) -> String {
        match self {
            StackEntry::String(s) => format!("\"{s}\""),
            StackEntry::Environment(e) => e.borrow().to_string(),
        }
    }

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
        return Err(message.to_string());
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
    let mut env = Environment::new_shared();

    run_program(&program, env)
}

fn run_program(program: &str, mut env: SharedEnvironment) -> Result<Stack, String> {
    let mut stack = vec![];

    let program = program.to_string();
    let mut program = parse(&program)?;
    program.reverse();

    // record all the TESTs we've done
    let mut history = Vec::<String>::new();

    // initialise our environment for DEFINE and LOOKUP
    // let mut env = Environment::new_shared();

    loop {
        if program.len() == 0 {
            return Ok(stack);
        }
        let cmd = program.pop().unwrap();
        match cmd {
            Command::String(s) => stack.push(make_sses(s)),
            Command::Symbol(s) => match s.as_str() {
                "DUP" => run_dup(&mut stack)?,
                "DEFINE" => run_define(&env, &mut stack)?,
                "LOOKUP" => run_lookup(&env, &mut stack)?,
                "EXECUTE" => run_execute(&mut program, &mut stack)?,
                "CREATE" => run_create(&mut stack),
                // in ENTER and LEAVE env is re-bound to a new value
                "ENTER" => env = run_enter(env, &mut stack)?,
                "LEAVE" => env = run_leave(env)?,
                "ERROR" => run_error(&mut stack)?,
                "STEQ" => run_steq(&mut stack)?,
                "JOIN" => run_join(&mut stack)?,
                "CHOP" => run_chop(&mut program, &mut stack)?,
                "TEST" => run_test(&env, &mut stack)?,
                "ASSERT" => run_assert(&env, &mut stack)?,
                // s is a Symbol, so "auto-execute" if it's defined
                _ => run_auto(env.clone(), &mut program, s, &mut stack)?,
            },
        }
    }
}

fn run_auto(
    env: SharedEnvironment,
    program: &mut Program,
    s: String,
    stack: &mut Stack,
) -> Result<(), String> {
    // lookup s in the current environment
    let def = env.borrow().lookup(s)?; // if not defined, throw error.
                                       // borrow the value through the Rc<RefCell<>> wrapper
    let bdef = def.borrow();
    // now we can handle the two cases
    match &*bdef {
        StackEntry::String(s) => {
            let command = Command::String(s.to_string());
            program.push(Command::Symbol("EXECUTE".to_string()));
            program.push(command);
            return Ok(());
        }
        StackEntry::Environment(_) => {
            stack.push(def.clone());
            return Ok(());
        }
    }
}

fn run_test(env: &SharedEnvironment, stack: &mut Stack) -> Result<(), String> {
    if stack.len() == 0 {
        return Err("TEST on empty stack".to_string());
    }
    let boolean = stack_pop_string(stack, "Expected boolean")?;
    let test_name = stack_pop_string(stack, "Expected test name")?;
    print!("TEST {test_name}...");
    if boolean != "true" {
        println!("TEST failed '{}'", test_name);
        // our TEST failed: report whole of stack
        return Err(format!("TEST '{test_name}' failed on false {:?}", stack));
    }
    if stack.len() > 0 {
        println!("TEST failed '{}'", test_name);
        let additional = stack.pop().unwrap();
        return Err(format!(
            "TEST '{test_name}' failed with extra stack entry '{:?}'",
            additional
        ));
    }

    if env.borrow().parent != None {
        println!("TEST failed '{}'", test_name);
        return Err(format!("TEST: '{test_name}' Not at outer environment"));
    }

    println!("passed.");
    // TEST passed so now just continue...
    Ok(())
}

fn run_assert(env: &SharedEnvironment, stack: &mut Stack) -> Result<(), String> {
    let program = stack_pop_string(stack, "ASSERT had no program")?;

    // run this program within ourselves
    let result = run_program(&program, env.borrow_mut().child_get());

    // only return true if there was a single-entry true left on stack
    if result.is_ok() {
        let result = result.clone().unwrap();
        if result.len() == 1 {
            if result[0] == make_sses("true".to_string()) {
                let se = make_sses("true".to_string());
                stack.push(se);
                return Ok(());
            }
        }
    }

    let se = make_sses("false".to_string());
    stack.push(se);
    Ok(())
}

fn run_dup(stack: &mut Stack) -> Result<(), String> {
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

fn run_define(env: &SharedEnvironment, stack: &mut Stack) -> Result<(), String> {
    let key = stack_pop_string(stack, "no key for DEFINE")?;
    let value = stack.pop();
    if value == None {
        return Err(format!("**No value found for {key}"));
    }
    let value = value.unwrap();
    if env.borrow().map.contains_key(&key) {
        return Err(format!("Attempting re-definition of {key}"));
    }
    env.borrow_mut().define(key, value);
    Ok(())
}

fn run_lookup(env: &SharedEnvironment, stack: &mut Stack) -> Result<(), String> {
    let key = stack_pop_string(stack, "no key for LOOKUP")?;
    let value = env.borrow().lookup(key)?;
    stack.push(value);
    Ok(())
}

fn run_execute(program: &mut Program, stack: &mut Stack) -> Result<(), String> {
    let subprogram = stack_pop_string(stack, "no string for EXECUTE")?;
    let mut cmds = parse(&subprogram)?;
    program.push(Command::Symbol("LEAVE".to_string()));
    cmds.reverse();
    program.extend(cmds);
    program.push(Command::Symbol("ENTER".to_string()));
    program.push(Command::Symbol("CREATE".to_string()));
    Ok(())
}

// Given a stack entry, we want to know if it's a String or
// SharedEnvironment.

impl StackEntry {
    fn is_string(&self) -> bool {
        match self {
            Self::String(_) => true,
            _ => false,
        }
    }
    /* TODO : Get address of the hashmap
    fn get_ptr<T>(&self)->*const T{
        match self{
            Self::String(_) => panic!("ptr not defined on strings"),
            Self::Environment(e) => &e.borrow().map as *const T,
        }
    }
    */
}

fn get_se(se: &StackEntry) -> Option<SharedEnvironment> {
    match se {
        StackEntry::String(_) => return None,
        StackEntry::Environment(se) => return Some(se.clone()),
    }
}

fn run_steq(stack: &mut Stack) -> Result<(), String> {
    //  pop all 4 arguments off the stack
    print_stderr("run_steq");

    let unequal_string = stack_pop_string(stack, "STEQ:no string")?;
    let equal_string = stack_pop_string(stack, "STEQ:no string")?;
    /*
    let s1 = stack_pop_string(stack, "STEQ:no string")?;
    let s2 = stack_pop_string(stack, "STEQ:no string")?;
    */
    let v1 = stack.pop().unwrap();
    let v2 = stack.pop().unwrap();
    // if both are strings, compare them using string equality
    if v1.borrow().is_string() && v2.borrow().is_string() {
        if v1 == v2 {
            stack.push(make_sses(equal_string));
        } else {
            stack.push(make_sses(unequal_string));
        };
        return Ok(());
    }
    // if both are environments, compare them
    if !v1.borrow().is_string() && !v2.borrow().is_string() {
        let se1 = get_se(&*v1.borrow()).unwrap();
        let se2 = get_se(&*v2.borrow()).unwrap();
        if Environment::shared_equals(se1, se2) {
            //if &*v1 == &*v2 {
            //if std::ptr::eq(&*v1,&*v2) {
            stack.push(make_sses(equal_string));
        } else {
            stack.push(make_sses(unequal_string));
        }
        return Ok(());
    }
    // so one is a string, one is an environment : they are different.
    stack.push(make_sses(unequal_string));
    Ok(())
}

fn run_leave(env: SharedEnvironment) -> Result<SharedEnvironment, String> {
    Ok(env.borrow().parent_get()?)
}

fn run_enter(env: SharedEnvironment, stack: &mut Stack) -> Result<SharedEnvironment, String> {
    let e = stack.pop();
    if e == None {
        return Err("ENTER on empty stack".to_string());
    }
    let se = get_env(e.unwrap());
    //  want se.parent to be env
    se.clone().borrow_mut().assign_parent(env.clone());
    return Ok(se);
}

fn run_create(stack: &mut Stack) {
    let se = StackEntry::Environment(Environment::new_shared());
    stack.push(make_sse(se));
}

fn run_error(stack: &mut Stack) -> Result<(), String> {
    match stack.len() {
        0 => Err("ERROR TERMINATION:Empty Stack".to_string()),
        _ => {
            let text = stack_pop_string(stack, "never fails")?;
            let r = format!("ERROR TERMINATION:{text}");
            Err(r)
        }
    }
}

fn run_chop(program: &mut Program, stack: &mut Stack) -> Result<(), String> {
    let s = &stack_pop_string(stack, "CHOP:no string")?;
    let l = s.len();
    if l == 0 {
        stack.push(make_sses("CHOP on empty string".to_string()));
        program.push(Command::Symbol("ERROR".to_string()));
    } else {
        let chopped = (s[..l - 1]).to_string();
        let final_char = (s[l - 1..]).to_string();
        stack.push(make_sses(chopped));
        stack.push(make_sses(final_char));
    }
    Ok(())
}

fn run_join(stack: &mut Stack) -> Result<(), String> {
    let s1 = stack_pop_string(stack, "JOIN:no string")?;
    let s2 = stack_pop_string(stack, "JOIN:no string")?;
    stack.push(make_sses(s2 + &s1));
    Ok(())
}

pub fn stack_to_string(stack: Stack) -> String {
    let mut r = vec![];
    r.push("[ ".to_string());
    let mut sr = vec![];
    for e in stack {
        sr.push(format!("{}", e.borrow().to_string()));
    }
    r.push(sr.join(", "));

    r.push(" ]".to_string());
    r.join("")
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
                let substring = convert_string(&bytes[start..stop]);
                return Err(format!("Bad substring in lex:{substring}"));
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
            Err(s) => assert_eq!(s, "Expected test name"),
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
    fn test_environment_usage() {
        let p1 = "CREATE [e]: e ENTER [[bar]][foo]: LEAVE e ENTER foo";
        let p2 = "[bar]";
        assert_eq_prelude(p1, p2);
    }

    #[test]
    fn test_formatted_output() {
        let r = run_with_prelude("[abc][def]").unwrap();
        println!("{}", stack_to_string(r));
        assert!(true);
    }

    #[test]
    fn test_prelude_runs_successfully() {
        let r = run_with_prelude("");
        assert!(r.is_ok());
    }

    #[test]
    fn test_test_inner_environment_failure() {
        let r = run("CREATE ENTER [this should fail] [true] TEST");
        assert!(r.is_err());
    }

    #[test]
    fn test_throws_on_redefinition() {
        let r = run("[foo][bar]DEFINE [another def][bar]DEFINE");
        assert!(r.is_err());
    }

    #[test]
    fn test_parse_bug() {
        let r = run_with_prelude("[abc");
        assert!(r.is_err());
    }
    #[test]
    fn test_steq_bug() {
        // STEQ should compare strings AND environments
        // note we ideally want to compare the contents of two environments
        // not their memory pointers
        assert_eq!(
            run("CREATE CREATE [1][2]STEQ").unwrap(),
            run("[1]").unwrap()
        );
        assert_eq!(run("CREATE DUP [1][2]STEQ").unwrap(), run("[1]").unwrap());
        assert_eq!(run("CREATE [a] [1][2]STEQ").unwrap(), run("[2]").unwrap());
        assert_eq!(run("[a] CREATE [1][2]STEQ").unwrap(), run("[2]").unwrap());
        assert_eq!(run("[a] [a] [1][2]STEQ").unwrap(), run("[1]").unwrap());
        assert_eq!(run("[b] [a] [1][2]STEQ").unwrap(), run("[2]").unwrap());
    }

    #[test]
    fn test_new_environments_differ() {
        // if we compare 2 new environments, they should differ
        let e1 = Environment::new();
        let e2 = Environment::new();
        assert!(!std::ptr::eq(&e1.map, &e2.map)); // using PartialOrd they are equal.
    }

    #[test]
    fn test_new_environments_behind_rcrefcell_differ() {
        let e1 = Environment::new_shared();
        let e2 = Environment::new_shared();
        assert!(!std::ptr::eq(&e1, &e2));
    }

    #[test]
    fn test_hashmaps_differ() {
        // we need a special comparison to check hashmap identity
        let h1 = HashMap::<i64, i64>::new();
        let h2 = HashMap::<i64, i64>::new();
        assert!(!std::ptr::eq(&h1, &h2));
    }

    #[test]
    fn test_assert_interprets_empty_string() {
        let p = "[]ASSERT";
        let r = run_with_prelude(p);
        assert!(r.is_ok());
        let r = r.unwrap();

        let expected = run_with_prelude("false").unwrap();
        assert_eq!(r, expected);
    }

    #[test]
    fn test_assert_throws_error_no_program() {
        let p = "ASSERT";
        let r = run_with_prelude(p);
        assert!(r.is_err());
    }

    #[test]
    fn test_assert_throws_error_on_program() {
        let p = "[something_undefined] ASSERT";
        let result = run_with_prelude(p).unwrap();
        let expected = run_with_prelude("false").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_assert_program_returns_true() {
        let p = "[true] ASSERT";
        let result = run_with_prelude(p).unwrap();
        let expected = run_with_prelude("true").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_assert_program_returns_false() {
        let p = "[false] ASSERT";
        let result = run_with_prelude(p).unwrap();
        let expected = run_with_prelude("false").unwrap();
        assert_eq!(result, expected);
    }

    #[test]
    fn test_assert_program_includes_new_definitions() {
        let p = "[[1]][something_new]: [something_new [1] eq] ASSERT";
        let result = run_with_prelude(p);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), run_with_prelude("true").unwrap());
    }

    // test Environment equality checking
    // envs must match depths, and all key-value members
    #[test]
    fn test_envs_different_depths() {
        let e1 = Environment::new_shared().borrow().child_get();
        let e2 = Environment::new_shared();
        assert!(!Environment::shared_equals(e1, e2));
    }

    #[test]
    fn test_local_keys_only_match() {
        let e1 = Environment::new_shared();
        let e2 = Environment::new_shared();
        let v = make_sses("foo".to_string());
        e1.borrow_mut().define("a".to_string(), v.clone());
        e2.borrow_mut().define("a".to_string(), v);
        assert!(Environment::shared_equals(e1, e2));
    }
    #[test]
    fn test_local_keys_differ_match() {
        let e1 = Environment::new_shared();
        let e2 = Environment::new_shared();
        let v1 = make_sses("foo".to_string());
        let v2 = make_sses("bar".to_string());
        e1.borrow_mut().define("a".to_string(), v1);
        e2.borrow_mut().define("a".to_string(), v2);
        assert!(!Environment::shared_equals(e1, e2));
    }

    #[test]
    fn test_parents_differ_match() {
        let e1 = Environment::new_shared().borrow_mut().child_get();
        let e2 = Environment::new_shared().borrow_mut().child_get();
        let v1 = make_sses("foo".to_string());
        let v2 = make_sses("bar".to_string());
        e1.borrow_mut()
            .parent_get()
            .unwrap()
            .borrow_mut()
            .define("b".to_string(), v1);
        e2.borrow_mut()
            .parent_get()
            .unwrap()
            .borrow_mut()
            .define("a".to_string(), v2);
        assert!(!Environment::shared_equals(e1, e2));
    }

    // keys all match
    // keys differ locally
    // local keys the same, but parent keys differ
}
