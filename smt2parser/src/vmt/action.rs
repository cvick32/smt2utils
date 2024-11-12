use crate::concrete::Command;



#[derive(Clone, Debug)]
pub struct Action {
    pub action: Command,
    pub relationship: Command,
}

impl Action {
    pub fn get_current_action_name(&self) -> &String {
        match &self.action {
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
    
    pub(crate) fn as_commands(&self) -> Vec<Command> {
        //(define-fun .grantExclusiveRule () Bool (! grantExclusiveRule :action 0))
        vec![self.action.clone(), self.relationship.clone()]
    }
}