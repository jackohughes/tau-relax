use crate::checker::{check_program, TypeCheckCtxt};
use crate::parser::parse;

const EXAMPLE_1: &str = "
    let r = newrgn in
    begin
      let l1 = 1 at r in 
      skip
      ||
      freergn r
    end
";

const EXAMPLE_2: &str = "
    let r = newrgn in
    let l1 = ref unset at r in 
    let l2 = ref unset at r in 
    begin
      set(l1);
      check l2 then freergn r else freergn r
      ||
      set(l2);
      check l1 then freergn r else freergn r
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