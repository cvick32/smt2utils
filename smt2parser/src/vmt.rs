use std::collections::HashMap;

use crate::concrete::{Command, Symbol, SyntaxBuilder, Term};

static PROPERTY_ATTRIBUTE: &str = "invar-property";
static TRANSITION_ATTRIBUTE: &str = "trans";
static INITIAL_ATTRIBUTE: &str = "init";

/// VMTModel represents a transition system given in VMT format. 
/// The VMT specification is no longer available but there is an example here:
/// https://es-static.fbk.eu/people/griggio/ic3ia/
/// The property is specifie
#[derive(Clone, Debug)]
pub struct VMTModel {
    sorts: Vec<Command>,
    state_variables: Vec<Variable>,
    actions: Vec<Action>,
    initial_condition: Term,
    transition_condition: Term,
    property_condition: Term,
}

impl VMTModel {
    pub fn checked_from(commands: Vec<Command>) -> Result<Self, ()> {
        let number_of_commands = commands.len();
        assert!(number_of_commands > 3, "Not enough commands for VMT model!");
        let property_condition: Term =
            get_transition_system_component(&commands[number_of_commands - 1], PROPERTY_ATTRIBUTE);
        let transition_condition: Term = get_transition_system_component(
            &commands[number_of_commands - 2],
            TRANSITION_ATTRIBUTE,
        );
        let initial_condition: Term =
            get_transition_system_component(&commands[number_of_commands - 3], INITIAL_ATTRIBUTE);
        let mut variable_commands: HashMap<String, Command> = HashMap::new();
        let mut sorts: Vec<Command> = vec![];
        let mut variable_relationships = vec![];
        for (i, command) in commands.iter().enumerate() {
            if i < number_of_commands - 3 {
                // Check whether a variable should be action, state, or local
                match command {
                    Command::DeclareFun {
                        symbol,
                        parameters: _,
                        sort: _,
                    } => {
                        variable_commands.insert(symbol.0.clone(), command.clone());
                    }
                    Command::DefineFun { sig: _, term: _ } => {
                        variable_relationships.push(command);
                    }
                    Command::DeclareSort {
                        symbol: _,
                        arity: _,
                    } => {
                        sorts.push(command.clone());
                    }
                    _ => {
                        panic!("Unknown VMT command: {:?}", command);
                    }
                }
            }
        }
        let (state_variables, actions) =
            get_variables_and_actions(variable_relationships, variable_commands);

        Ok(VMTModel {
            sorts,
            state_variables,
            actions,
            initial_condition,
            transition_condition,
            property_condition,
        })
    }

    pub fn print_stats(&self) {
        println!("Number of Variables: {}", self.state_variables.len());
        println!("Number of Actions: {}", self.actions.len());
        println!("Number of Sorts: {}", self.sorts.len());
    }

    pub fn print_raw_smtlib2(&self) {
        for sort in &self.sorts {
            println!("{}", sort.clone().accept(&mut SyntaxBuilder).unwrap())
        }
        for var in &self.state_variables {
            println!(
                "{}",
                var.current.clone().accept(&mut SyntaxBuilder).unwrap()
            );
        }
        for action in &self.actions {
            println!(
                "{}",
                action
                    .action_command
                    .clone()
                    .accept(&mut SyntaxBuilder)
                    .unwrap()
            );
        }
        println!(
            "INIT: {}",
            self.initial_condition
                .clone()
                .accept(&mut SyntaxBuilder)
                .unwrap()
        );
        println!(
            "TRANS: {}",
            self.transition_condition
                .clone()
                .accept(&mut SyntaxBuilder)
                .unwrap()
        );
        println!(
            "PROP: {}",
            self.property_condition
                .clone()
                .accept(&mut SyntaxBuilder)
                .unwrap()
        );
    }

    pub fn unroll(&self, length: u8) -> SMTProblem {
        let mut builder = VMTBuilder {
            visitor: SyntaxBuilder,
            current_variables: self.get_all_current_variable_names(),
            next_variables: self.get_all_next_variable_names(),
            step: 0,
        };
        let mut smt_problem = SMTProblem::new(&self.sorts);

        smt_problem.add_assertion(&self.initial_condition, builder.clone());
        for _ in 0..length {
            // Must add variable definitions for each variable at each time step.
            smt_problem.add_definitions(&self.state_variables, &self.actions, builder.clone());
            smt_problem.add_assertion(&self.transition_condition, builder.clone());
            builder.add_step();
        }
        // Don't forget the variable definitions at time `length`.
        smt_problem.add_definitions(&self.state_variables, &self.actions, builder.clone());
        smt_problem.add_property_assertion(&self.property_condition, builder.clone());
        assert!(
            smt_problem.init_and_trans_assertions.len() == (length + 1).into(),
            "Unrolling gives incorrect number of steps {} for length {}.",
            smt_problem.init_and_trans_assertions.len(),
            length
        );
        smt_problem
    }

    fn get_all_current_variable_names(&self) -> Vec<String> {
        let mut state_variable_names: Vec<String> = self
            .state_variables
            .iter()
            .map(|var| var.get_current_variable_name().clone())
            .collect();
        let mut action_names: Vec<String> = self
            .actions
            .iter()
            .map(|action| action.get_current_action_name().clone())
            .collect();
        state_variable_names.append(&mut action_names);
        state_variable_names
    }

    fn get_all_next_variable_names(&self) -> HashMap<String, String> {
        self.state_variables
            .iter()
            .map(|var| {
                (
                    var.get_next_variable_name().clone(),
                    var.get_current_variable_name().clone(),
                )
            })
            .collect()
    }
}

#[derive(Default)]
pub struct SMTProblem {
    sorts: Vec<Command>,
    definitions: Vec<Command>,
    init_and_trans_assertions: Vec<Term>,
    property_assertion: Option<Term>,
}

impl SMTProblem {
    fn new(sorts: &Vec<Command>) -> Self {
        Self {
            sorts: sorts.clone(),
            definitions: vec![],
            init_and_trans_assertions: vec![],
            property_assertion: None
        }
    }

    fn add_assertion(&mut self, condition: &Term, mut builder: VMTBuilder) {
        let rewritten_condition = condition.clone().accept(&mut builder).unwrap();
        self.init_and_trans_assertions.push(rewritten_condition);
    }

    /// Need to assert the negation of the property given in the VMTModel for BMC.
    fn add_property_assertion(&mut self, condition: &Term, mut builder: VMTBuilder) {
        let rewritten_property = condition.clone().accept(&mut builder).unwrap();
        self.property_assertion = Some(rewritten_property);
    }

    fn add_definitions(
        &mut self,
        state_variables: &Vec<Variable>,
        actions: &Vec<Action>,
        mut builder: VMTBuilder,
    ) {
        for state_variable in state_variables {
            let definition_at_time = state_variable.current.clone().accept(&mut builder).unwrap();
            self.definitions.push(definition_at_time);
        }
        for action in actions {
            let action_at_time = action.action_command.clone().accept(&mut builder).unwrap();
            self.definitions.push(action_at_time);
        }
    }
    pub fn to_smtlib2(&self) -> String {
        assert!(self.property_assertion.is_some(), "No property assertion for SMTProblem!");
        let sort_names = self.sorts.iter().map(|sort| sort.to_string()).collect::<Vec<String>>().join("\n");
        let defs = self.definitions.iter().map(|def| def.to_string()).collect::<Vec<String>>().join("\n");
        let init_and_trans_asserts = self.init_and_trans_assertions.iter().map(|assert_term| assert(assert_term)).collect::<Vec<String>>().join("\n");
        let prop = self.property_assertion.clone().unwrap();
        let property_assert = assert_negation(&prop);
        format!("{}\n{}\n{}\n{}", sort_names, defs, init_and_trans_asserts, property_assert)
    }
}

#[derive(Clone, Debug)]
pub struct Variable {
    current: Command,
    next: Command,
}

impl Variable {
    fn get_current_variable_name(&self) -> &String {
        match &self.current {
            Command::DeclareFun {
                symbol,
                parameters: _,
                sort: _,
            } => {
                return &symbol.0;
            }
            _ => panic!("Variable's current Command must be DeclareFun."),
        }
    }

    fn get_next_variable_name(&self) -> &String {
        match &self.next {
            Command::DeclareFun {
                symbol,
                parameters: _,
                sort: _,
            } => {
                return &symbol.0;
            }
            _ => panic!("Variable's next Command must be DeclareFun."),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Action {
    action_command: Command,
}

impl Action {
    fn get_current_action_name(&self) -> &String {
        match &self.action_command {
            Command::DeclareFun {
                symbol,
                parameters: _,
                sort: _,
            } => {
                return &symbol.0;
            }
            _ => panic!("Actions's Command must be DeclareFun."),
        }
    }
}

fn assert(term: &Term) -> String {
    format!("(assert {})", term)
}

fn assert_negation(term: &Term) -> String {
    format!("(assert (not {}))", term)
}

fn get_variables_and_actions(
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
                        });
                    } else if keyword_string == ":action" {
                        let action_variable_name = scrub_variable_name(term.to_string());
                        if variable_commands.contains_key(&action_variable_name) {
                            for (variable_name, action_command) in &variable_commands {
                                if action_variable_name == *variable_name {
                                    actions.push(Action {
                                        action_command: action_command.clone(),
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

fn scrub_variable_name(variable_name: String) -> String {
    if variable_name.starts_with("|") && variable_name.ends_with("|") {
        let mut chars = variable_name.chars();
        chars.next();
        chars.next_back();
        chars.as_str().to_string()
    } else {
        variable_name
    }
}

fn get_variable_command(
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

fn get_transition_system_component(command: &Command, attribute: &str) -> Term {
    if command_has_attribute_string(command, attribute) {
        match command {
            Command::DefineFun { sig: _, term } => match term {
                Term::Attributes {
                    term,
                    attributes: _,
                } => {
                    return *term.clone();
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

fn command_has_attribute_string(command: &Command, attribute: &str) -> bool {
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

#[derive(Clone)]
struct VMTBuilder {
    visitor: SyntaxBuilder,
    current_variables: Vec<String>,
    next_variables: HashMap<String, String>,
    step: u8,
}

impl VMTBuilder {
    pub fn add_step(&mut self) {
        self.step += 1;
    }
}

impl crate::rewriter::Rewriter for VMTBuilder {
    type V = SyntaxBuilder;
    type Error = crate::concrete::Error;

    fn visitor(&mut self) -> &mut Self::V {
        &mut self.visitor
    }

    fn process_symbol(&mut self, s: Symbol) -> Result<Symbol, Self::Error> {
        if self.current_variables.contains(&s.0) {
            Ok(Symbol(format!("{}@{}", s.0, &self.step.to_string())))
        } else if self.next_variables.contains_key(&s.0) {
            let next = self.step + 1;
            let current_variable_name = self.next_variables.get(&s.0).unwrap();
            Ok(Symbol(format!(
                "{}@{}",
                current_variable_name,
                &next.to_string()
            )))
        } else {
            Ok(s)
        }
    }
}
