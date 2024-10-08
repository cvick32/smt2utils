extern crate z3;
extern crate z3tracer;
use std::{
    collections::HashMap,
    fs,
    path::PathBuf,
};
use z3::{Config, Context, SatResult, Solver};
use z3tracer::{
    get_instantiations, parser::ParserConfig, report::process_file,
    syntax::Ident, Model, ModelConfig,
};

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

    let mut p_config = ParserConfig::default();
    p_config.skip_z3_version_check = true;
    let mut model_config = ModelConfig::default();
    model_config.parser_config = p_config;

    let model = process_file(model_config, &PathBuf::from("./z3_logs/german.log"));

    match model {
        Ok(model) => {
            //println!("Model: {:#?}", model);
            println!("Rough num conflicts: {:#?}", model.conflicts().size_hint());
            println!("Num instansitations: {}", model.instantiations().len());
            println!(
                "Most instansiated terms: {:#?}",
                model.most_instantiated_terms()
            );
            let (times, id) = model.most_instantiated_terms().pop().unwrap();
            println!("Instantiations: {:?}", get_instantiations(&model));

            for dd in model.most_instantiated_terms() {
                println!("INST: {} {:?}", dd.0, dd.1);
            }

            let mut timestamp_to_id = HashMap::new();
            for (id, data) in model.terms() {
                timestamp_to_id.insert(data.timestamp, id);
            }

            for (inst_type, timestamps) in get_instantiations(&model) {
                println!("Instantiations for {}:", inst_type);
                for timestamp in timestamps {
                    // Subtract 1 to get the reference to the actual term and not the application.
                    let term = timestamp_to_id.get(&(timestamp - 1)).unwrap();
                    let decoded = decode_array_instantiation(&model, &term);
                    match decoded {
                        Ok(inst_decoded) => println!("timestamp {}: {}", timestamp, inst_decoded),
                        Err(_) => println!("Timestamp {} failed to decode!", timestamp),
                    }
                }
            }
        }
        Err(z3_tracer_error) => {
            panic!("Z3Tracer failed: {}", z3_tracer_error);
        }
    }
}

fn decode_array_instantiation(model: &Model, id: &Ident) -> Result<String, ()> {
    match model.term(id) {
        Ok(term) => match term {
            z3tracer::syntax::Term::App {
                name,
                args,
                meaning,
            } => {
                if args.is_empty() {
                    Ok(name.to_string())
                } else {
                    let args = args
                        .iter()
                        .map(|arg| decode_array_instantiation(model, arg).unwrap())
                        .collect::<Vec<String>>()
                        .join(" ");
                    Ok(format!("({} {})", name, args))
                }
            }
            z3tracer::syntax::Term::Var { index } => Ok(format!("{}", index)),
            z3tracer::syntax::Term::Quant {
                name,
                params,
                triggers,
                body,
                var_names,
            } => {
                let var_name_string = match var_names {
                    Some(names) => {
                        names.iter().map(|var| format!("{}: {}", var.name.0, var.sort.0)).collect::<Vec<String>>().join(" ")
                    }
                    None => "".to_string(),
                };
                Ok(format!("(Q ({}): {}", var_name_string, decode_array_instantiation(model, body).unwrap()))
            }
            z3tracer::syntax::Term::Lambda {
                name,
                params,
                triggers,
                body,
            } => todo!(),
            z3tracer::syntax::Term::Proof {
                name,
                args,
                property,
            } => todo!(),
            z3tracer::syntax::Term::Builtin { name } => todo!(),
        },
        _ => Err(()),
    }
}
