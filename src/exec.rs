use thiserror::Error;

/// Represents the result of a successful execution.
pub enum StepResult {
    Unremarkable,
    ECall,
    EBreak,
}
/// Represents an error during execution.
#[derive(Clone, Copy, Debug, Error, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExecutionError {
    #[error("encountered illegal instruction")]
    IllegalInstruction,
    #[error("encountered instruction with an unsupported length")]
    UnsupportedLength,
    #[error("encountered unimplemented instruction")]
    Unimplemented,
}
