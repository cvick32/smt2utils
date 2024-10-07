extern crate z3;
use z3::*;

use std::fs;

fn main() {
    let config = Config::new();
    let context = Context::new(&config);
    let solver = Solver::new(&context);

    let vmt = fs::read("./examples/test.smt2").expect("Unable to read VMT file.");
    
    solver.from_string(vmt);

    match solver.check() {
        SatResult::Unsat => todo!(),
        SatResult::Unknown => todo!(),
        SatResult::Sat => println!("{:?}", solver.get_model().unwrap()),
    }
}
