use nom::error::{ContextError, ParseError};
use nom_locate::LocatedSpan;

pub type Span<'a> = LocatedSpan<&'a str>;
