use std::collections::HashMap;

use crate::concrete::{Command, Term};

use super::{action::Action, variable::Variable};


pub fn assert_term(term: &Term) -> String {
    format!("(assert {})", term)
}

pub fn assert_negation(term: &Term) -> String {
    format!("(assert (not {}))", term)
}

pub fn get_variables_and_actions(
    variable_relationships: Vec<&Command>,
    variable_commands: HashMap<String, Command>,
) -> (Vec<Variable>, Vec<Action>) {
    let mut state_variables: Vec<Variable> = vec![];
    let mut actions: Vec<Action> = vec![];
    for variable_relationship in variable_relationships {
        match variable_relationship {
            Command::DefineFun { sig: _, term } => match term {
                Term::Attributes { term, attributes } => {
                    assert!(attributes.len() == 1);
                    let (keyword, value) = &attributes[0];
                    let keyword_string = keyword.to_string();
                    if keyword_string == ":next" {
                        let variable_command = get_variable_command(
                            scrub_variable_name(term.to_string()),
                            &variable_commands,
                        );
                        let new_variable_command = get_variable_command(
                            scrub_variable_name(value.to_string()),
                            &variable_commands,
                        );
                        state_variables.push(Variable {
                            current: variable_command,
                            next: new_variable_command,
                            relationship: variable_relationship.clone(),
                        });
                    } else if keyword_string == ":action" {
                        let action_variable_name = scrub_variable_name(term.to_string());
                        if variable_commands.contains_key(&action_variable_name) {
                            for (variable_name, action_command) in &variable_commands {
                                if action_variable_name == *variable_name {
                                    actions.push(Action {
                                        action: action_command.clone(),
                                        relationship: variable_relationship.clone(),
                                    });
                                    break;
                                }
                            }
                        } else {
                            panic!("Proposed action variable {} not previously defined.", term);
                        }
                    } else {
                        panic!("Only `next` and `action` keyword attributes are allowed in variable relationships found: {}", keyword_string);
                    }
                }
                _ => panic!("Only Attribute terms can define variable relationships."),
            },
            _ => panic!("Variable Relationship is not a (define-fun)."),
        }
    }
    (state_variables, actions)
}

pub fn scrub_variable_name(variable_name: String) -> String {
    if variable_name.starts_with("|") && variable_name.ends_with("|") {
        let mut chars = variable_name.chars();
        chars.next();
        chars.next_back();
        chars.as_str().to_string()
    } else {
        variable_name
    }
}

pub fn get_variable_command(
    variable_name: String,
    variable_commands: &HashMap<String, Command>,
) -> Command {
    match variable_commands.get(&variable_name) {
        Some(command) => command.clone(),
        None => panic!(
            "First term in define-fun must be a variable name: {}",
            variable_name
        ),
    }
}

pub fn get_transition_system_component(command: &Command, attribute: &str) -> Term {
    if command_has_attribute_string(command, attribute) {
        match command {
            Command::DefineFun { sig: _, term } => match term {
                Term::Attributes {
                    term,
                    attributes,
                } => {
                    if attributes[0].0.0 != attribute {
                        panic!(
                            "Ill-formed system component: {}.\nShould have {} as attribute.",
                            command, attribute
                        );
                    }
                    return Term::Attributes { term: term.clone(), attributes: attributes.clone() }
                }
                _ => panic!("{}: Must have attribute.", attribute),
            },
            _ => panic!("{}: Command must be define-fun", attribute),
        }
    } else {
        panic!(
            "Ill-formed system component: {}.\nShould have {} as attribute.",
            command, attribute
        );
    }
}

pub fn command_has_attribute_string(command: &Command, attribute: &str) -> bool {
    match command {
        Command::DefineFun { sig: _, term } => match term {
            Term::Attributes {
                term: _,
                attributes,
            } => {
                assert!(attributes.len() == 1);
                let keyword = &attributes[0].0 .0;
                keyword == attribute
            }
            _ => false,
        },
        _ => false,
    }
}