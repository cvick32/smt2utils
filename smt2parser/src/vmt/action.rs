use crate::concrete::Command;



#[derive(Clone, Debug)]
pub struct Action {
    pub action_command: Command,
}

impl Action {
    pub fn get_current_action_name(&self) -> &String {
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