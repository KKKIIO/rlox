#[derive(Debug)]
pub struct InterpreteError {
    pub message: String,
    pub line: u32,
}
