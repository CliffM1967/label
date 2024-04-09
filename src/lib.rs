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

use std::collections::HashMap;
use std::io::{stderr, stdout, Write};

#[derive(Debug, PartialEq)]
pub enum Token {
    String(String),
    Symbol(String),
}

struct Environment {
    map: HashMap<String, String>,
    parent: Option<Box<Environment>>,
}

impl Environment {
    fn new() -> Self {
        let m = HashMap::new();
        Self {
            map: m,
            parent: None,
        }
    }

    fn child_get(self) -> Environment {
        let mut new_env = Self::new();
        new_env.parent = Some(Box::new(self));
        new_env
    }

    fn parent_get(self) -> Result<Environment, String> {
        if self.parent.is_none() {
            return Err("Cannot get parent environment".to_string());
        }
        Ok(*self.parent.unwrap())
    }

    fn define(&mut self, key: String, value: String) {
        self.map.insert(key, value);
    }

    fn lookup(&self, key: String) -> Result<String, String> {
        if self.map.contains_key(&key) {
            return Ok(self.map.get(&key).unwrap().to_string());
        }
        if self.parent.is_none() {
            return Err(format!("Cannot lookup '{key}'"));
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
fn option_to_result<T>(option: Option<T>, message: &str) -> Result<T, String> {
    match option {
        None => Err(message.to_string()),
        Some(x) => Ok(x),
    }
}

fn stack_pop(stack: &mut Vec<String>, message: &str) -> Result<String, String> {
    option_to_result(stack.pop(), message)
}

fn _prelude() -> String {
    "".to_string()
}

fn prelude() -> String {
    "
    
    [ Here is where we bootstrap our little language]
    [ It is clear that this is a comment, and it is polluting the stack!]
    [ So the first thing to do is to define a word to drop the TOS]
    [ And then use that to clean up our comments]

    [[a]DEFINE][pop]DEFINE

    [ For brevity we define ';' to be pop ]
    [pop][;]DEFINE

    [ We now have 6 comment-strings on the stack, so drop them];;; ;;;


    [][true] TEST   [ assert the stack is now empty ];

    [ for brevity, we define ':' to be DEFINE ];
    [PARENT DEFINE CHILD][:]DEFINE  

    [ nicer to write '?' rather than 'LOOKUP' ];
    [LOOKUP][?]:
    
    [ now define the words 'true' and 'false' ];
    [[true]][true]:
    [[false]][false]:

    [true false STEQ][eq]:  [ defines equality ];
    [str_eq1][a][a]eq TEST
    [str_eq2][a][b]eq false eq TEST
    
    [ implement dup to copy TOS ];
    [[a]: [a]? [a]?][dup]:

    [dup1][1]dup eq TEST

    [ swap to swap TOS and TOS-1];
    [[a]: [b]: [a]? [b]?][swap]:

    

    [ develop if-statement ];
    [ [boolean]:[false_block]:[true_block]:    [pull off the arguments];
      true boolean [true_block]? [false_block]? STEQ EXECUTE]
    [if]:

    [if1] [[1]][[2]]true  if [1]eq TEST
    [if2] [[1]][[2]]false if [2]eq TEST

    [ instead of writing [] true TEST we write assert_empty ];
    [[assert_empty failed]true TEST][assert_empty]:

    [ we need only implement nand.  Can then derive not,and & or];

    [ nand : only return false when both inputs true ];
    [ [b]: [a]:
        [[false][true]b if]
        [true]
        a 
        if
    ][nand]: 

    [nand1] true  true    nand false eq TEST 
    [nand2] true  false   nand true  eq TEST 
    [nand3] false true    nand true  eq TEST 
    [nand4] false false   nand true  eq TEST 

    [dup nand][not]:

    [not1]false not TEST  
    [not2]true not false eq TEST 

    [ boolean-and : True only when both args are True];

    [nand not][and]:

    [and1] true  true   and true  eq TEST
    [and2] true  false  and false eq TEST
    [and3] false true   and false eq TEST
    [and4] false false  and false eq TEST

    [ boolean-or : True when either arg is true];

    [not swap not nand][or]:

    [or1] true  true   or true  eq TEST
    [or2] true  false  or true eq TEST
    [or3] false true   or true eq TEST
    [or4] false false  or false eq TEST
    
    [implement string reversal recursively];

    [[s]:
        [[]]
        [[s]? CHOP swap reverse JOIN ]
        [s]? [] eq if

    ]
    [reverse]:

    [reverse1] []reverse []eq TEST
    [reverse2] [a]reverse [a]eq TEST
    [reverse3] [abc]reverse [cba]eq TEST 


    [implement zero as an empty string]; 
    [[]][nat_0]:

    [ nat_equals is simply eq : ];
    [eq][nat_eq]:

    [implement a successor function: Add one char to a given string];
    [[*] JOIN][nat_succ]:

    [implement a few numbers for later use];
    [nat_0 nat_succ][nat_1]:
    [nat_1 nat_succ][nat_2]:
    [nat_2 nat_succ][nat_3]:
    [nat_3 nat_succ][nat_4]:
    [nat_4 nat_succ][nat_5]:
    [nat_5 nat_succ][nat_6]:
    [nat_4 nat_succ][nat_5]:

    [addition is easy -- just JOIN two numbers together];
    [JOIN][nat_add]:

    [add1] nat_1 nat_2 nat_add nat_3 eq TEST  [ tests 1+2=3 ];

    [ for subtraction, we're going to need a decrement function nat_dec ];
    [ we need to check the zero case ];

    [ [t]: [[nat_dec called on nat_0] ERROR]
           [[t]? CHOP pop] 
           [t]? nat_0 eq if
    ][nat_dec]:


    [ comparing two nats can be done via eq];
    [eq][nat_eq]:

    [ now consider subtraction: we need repeated decrements];
    [ the base case is 'x 0 sub' should be 'x'];
    [ the recursive case is 'x y sub' should be 'x nat_dec y nat_dec];

    [ [y]: [x]:
        [[x]?]
        [[x]? nat_dec [y]? nat_dec nat_sub]
        [y]? nat_0 nat_eq if
    ][nat_sub]:

    [sub1] nat_1 nat_1 nat_sub nat_0 nat_eq TEST
    [sub2] nat_5 nat_3 nat_sub nat_2 nat_eq TEST

    [ want nat_lt and nat_gt ];
    
    [ [y]: [x]:
        [[true][false][y]? nat_0 eq if]
        [[x]? nat_dec [y]? nat_dec nat_gte ]
        [y]? nat_0 eq [x]? nat_0 eq or if
    ][nat_gte]:

    [gte1] nat_1 nat_1 nat_gte TEST
    [gte2] nat_1 nat_0 nat_gte TEST
    [gte3] nat_2 nat_3 nat_gte not TEST

    [ [y]: [x]: 
        [x]? [y]? nat_gte [x]? [y]? nat_eq not and
    ][nat_gt]:

    [gt1] nat_1 nat_0 nat_gt TEST
    [gt2] nat_1 nat_1 nat_gt not TEST
    [gt1] nat_1 nat_2 nat_gt not TEST


    [ nat_gt not ][nat_lte]:

    [lte1] nat_1 nat_0 nat_lte not TEST
    [lte2] nat_1 nat_1 nat_lte TEST
    [lte3] nat_1 nat_2 nat_lte TEST

    [ nat_gte not][nat_lt]:

    [lt1] nat_1 nat_0 nat_lt not TEST
    [lt2] nat_1 nat_1 nat_lt not TEST
    [lt3] nat_1 nat_2 nat_lt TEST

    [[i]:
        [nat_1]
        [[i]? nat_dec fib [i]?nat_dec nat_dec fib nat_add]
        [i]? nat_3 nat_lt if
    ][fib]:

    [ multplication is repeated addition ];
    [ for x*y we have the base case x*0=0 ];
    [ and x*y = x*(y-1) + x ];
    [
        [y]: [x]:
        [nat_0]
        [
            [[x]?]
            [[x]? [y]? nat_dec nat_times [x]? nat_add] 
            [y]? nat_0 eq if
        ]
        [y]? nat_0 eq if
    ][nat_times]:
    
    [nat_times1] nat_1 nat_1 nat_times nat_1 nat_eq TEST
    [nat_times2] nat_2 nat_2 nat_times nat_4 nat_eq TEST
    [nat_times3] nat_3 nat_2 nat_times nat_6 nat_eq TEST


[
    [ a new version of TEST which checks the top two items of the stack];
    [[y]: [x]: [y]? eq [x]? eq and TEST]
    [TEST2]:

    [TEST2] nat_1 nat_2 nat_1 nat_2 TEST2
];

    [ to compute x / y we repeatedly subtract y from x until ];
    [ we can go no further, and report the quotient ];

    [
        [y]: [x]:
        [
            [nat_1]
            [nat_0]
            [x]? [y]? nat_eq if
        ]
        [[x]? [y]? nat_sub [y]? nat_divide nat_1 nat_add]
        [x]? [y]? nat_lte if
    ][nat_divide]:

    [divide1]nat_1 nat_1 nat_divide nat_1 nat_eq TEST
    [divide2]nat_1 nat_2 nat_divide nat_0 nat_eq TEST
    [divide3]nat_3 nat_2 nat_divide nat_1 nat_eq TEST
    [divide4]nat_4 nat_2 nat_divide nat_2 nat_eq TEST

    [
        [y]: [x]:
        [x]? [y]? nat_divide [y]? nat_times [x]? swap nat_sub
    ][nat_remainder]:


    [rem1] nat_1 nat_1 nat_remainder nat_0 nat_eq TEST
    [rem2] nat_1 nat_2 nat_remainder nat_1 nat_eq TEST
    [rem3] nat_3 nat_2 nat_remainder nat_1 nat_eq TEST
    [rem4] nat_2 nat_3 nat_remainder nat_2 nat_eq TEST
    [rem5] nat_6 nat_3 nat_remainder nat_0 nat_eq TEST
    [rem6] nat_6 nat_4 nat_remainder nat_2 nat_eq TEST

    assert_empty
    
    "
    .to_string()
}

// what we run in the tests
fn run(program: &str) -> Result<Vec<String>, String> {
    run_with_passed_prelude(program, "".to_string())
}

// what we run in main.rs
pub fn run_with_prelude(program: &str) -> Result<Vec<String>, String> {
    run_with_passed_prelude(program, prelude())
}

// both of the above call this function
fn run_with_passed_prelude(program: &str, prelude: String) -> Result<Vec<String>, String> {
    // prefix the prelude with a space
    let program = format!("{} {}", prelude, program);
    let mut program = parse(&program)?;
    // going to be popping the commands off, so reverse the parse() result
    program.reverse();

    let mut stack = vec![];

    // initialise our environment for DEFINE and LOOKUP
    let mut env = Environment::new();

    loop {
        //for cmd in parse(program)? {
        if program.len() == 0 {
            return Ok(stack);
        }
        let cmd = program.pop().unwrap();
        //println!("Executing {:?}", cmd);
        match cmd {
            Command::String(s) => stack.push(s),
            Command::Symbol(s) => match s.as_str() {
                "DUP" => {
                    let tos = stack_pop(&mut stack, "Empty stack for DUP")?;
                    stack.push(tos.clone());
                    stack.push(tos);
                }
                "DEFINE" => {
                    let key = stack_pop(&mut stack, "no key for DEFINE")?;
                    let value = stack_pop(&mut stack, &format!("no value for DEFINE '{key}'"))?;
                    env.define(key, value);
                }
                "LOOKUP" => {
                    let key = stack_pop(&mut stack, "no key for LOOKUP")?;
                    let value = env.lookup(key)?;
                    stack.push(value);
                }
                "EXECUTE" => {
                    let subprogram = stack_pop(&mut stack, "no string for EXECUTE")?;
                    let mut cmds = parse(&subprogram)?;
                    program.push(Command::Symbol("PARENT".to_string()));
                    cmds.reverse();
                    program.extend(cmds);
                    program.push(Command::Symbol("CHILD".to_string()));
                }
                "CHILD" => env = env.child_get(),
                "PARENT" => env = env.parent_get()?,
                "ERROR" => match stack.len() {
                    0 => return Err("ERROR TERMINATION:Empty Stack".to_string()),
                    _ => {
                        let text = stack_pop(&mut stack, "foo")?;
                        let r = format!("ERROR TERMINATION:{text}");
                        return Err(r);
                    }
                },

                "STEQ" => {
                    //  pop all 4 arguments off the stack
                    let unequal_string = stack_pop(&mut stack, "STEQ:no string")?;
                    let equal_string = stack_pop(&mut stack, "STEQ:no string")?;
                    let s1 = stack_pop(&mut stack, "STEQ:no string")?;
                    let s2 = stack_pop(&mut stack, "STEQ:no string")?;
                    if s1 == s2 {
                        stack.push(equal_string);
                    } else {
                        stack.push(unequal_string);
                    }
                }
                "JOIN" => {
                    let s1 = stack_pop(&mut stack, "JOIN:no string")?;
                    let s2 = stack_pop(&mut stack, "JOIN:no string")?;
                    stack.push(s2 + &s1);
                }
                "CHOP" => {
                    let s1 = &stack_pop(&mut stack, "CHOP:no string")?;
                    let l = s1.len();
                    if l == 0 {
                        stack.push("CHOP on empty string".to_string());
                        program.push(Command::Symbol("ERROR".to_string()));
                    } else {
                        let chopped = (s1[..l - 1]).to_string();
                        let final_char = (s1[l - 1..]).to_string();
                        stack.push(chopped);
                        stack.push(final_char);
                    }
                }
                "TEST" => {
                    if stack.len() == 0 {
                        return Err("TEST on empty stack".to_string());
                    }
                    let boolean = stack.pop().unwrap();
                    let test_name = stack.pop();
                    if test_name == None {
                        return Err("TEST on stack without name".to_string());
                    }
                    let test_name = test_name.unwrap();
                    if boolean != "true" {
                        // our TEST failed: report whole of stack
                        return Err(format!("TEST '{test_name}' failed on false {:?}", stack));
                    }
                    if stack.len() > 0 {
                        let additional = stack.pop().unwrap();
                        return Err(format!(
                            "TEST '{test_name}' failed with extra stack entry '{additional}'"
                        ));
                    }
                    // everything passed so now just continue...
                }

                _ => {
                    // stop auto_exection on underscore...
                    if s.starts_with("_"){
                        program.push(Command::String(s));
                    }else{
                        let def = env.lookup(s)?;
                        program.push(Command::Symbol("EXECUTE".to_string()));
                        program.push(Command::String(def));
                    }
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
    fn test_execute() {
        // put a string on the stack, and then execute it...
        let result = run("[[a] [b]]EXECUTE");
        let expected = vec!["a".to_string(), "b".to_string()];
        assert_eq!(result, Ok(expected));
    }

    fn assert_eq(p1: &str, p2: &str) {
        let r1 = run(p1);
        let r2 = run(p2);
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
    fn test_new_dup() {
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
    fn test_string_equality() {
        let p = "[[T][F]STEQ][str_eq]DEFINE  [a][a]str_eq";
        assert_eq(p, "[T]");

        let p = "[[T][F]STEQ][str_eq]DEFINE  [a][b]str_eq";
        assert_eq(p, "[F]");
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
            Err(s) => assert_eq!(s, "TEST on stack without name"),
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
        match run("[YYY][XXX][true] TEST") {
            Ok(stack) => assert_eq!(stack.len(), 0),
            Err(s) => assert_eq!(s, "TEST 'XXX' failed with extra stack entry 'YYY'"),
        }

        // this is the passing case. We expect no error, and just to
        // pass...
        match run("[XXX][true] TEST") {
            Err(_) => panic!("TEST failed but should have passed"),
            _ => (),
        }
    }

    #[test]
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
