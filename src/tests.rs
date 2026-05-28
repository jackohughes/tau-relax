use crate::checker::{check_program, TypeCheckCtxt};
use crate::parser::parse;

const EXAMPLE_1: &str = "
    let r = newrgn in
    begin
      skip
      ||
      skip;
      freergn r
    end
";

pub fn test_example() {
    println!("parsing...");
    let program = match parse(EXAMPLE_1) {
        Ok(p) => {
            println!("parse ok");
            p
        }
        Err(errs) => {
            eprintln!("parse failed:");
            for e in errs {
                eprintln!("  {}", e);
            }
            std::process::exit(1);
        }
    };

    println!("typechecking...");
    let mut ctxt = TypeCheckCtxt::new();
    match check_program(&program, &mut ctxt) {
        Ok(_) => println!("typecheck ok"),
        Err(e) => {
            eprintln!("typecheck failed: {:?}", e);
            std::process::exit(1);
        }
    }
}