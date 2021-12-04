use nom::{
    branch::alt,
    bytes::complete::{tag, take_until},
    character::complete::{line_ending, multispace1, not_line_ending},
    combinator::{cut, opt, recognize},
    error::{ContextError, ParseError},
    multi::many0,
    sequence::tuple,
    IResult,
};

use super::parse::Span;

fn line_comment<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Span, E> {
    recognize(tuple((tag("//"), cut(not_line_ending), opt(line_ending))))(input)
}

fn block_comment<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Span, E> {
    recognize(tuple((tag("/*"), cut(take_until("*/")), cut(tag("*/")))))(input)
}

pub fn comment_whitespace0<'a, E: ParseError<Span<'a>> + ContextError<Span<'a>>>(
    input: Span<'a>,
) -> IResult<Span, Span, E> {
    recognize(many0(alt((line_comment, block_comment, multispace1))))(input)
}

mod test {
    use std::error::Error;

    use super::*;
    #[test]
    fn test_line_comment() {
        let input = Span::new("// This is a comment");
        let (rest, res) = line_comment::<nom::error::Error<Span>>(input).unwrap();
        assert_eq!(rest.fragment(), &"");
        assert_eq!(res.fragment(), input.fragment());

        let input = Span::new("// This is a comment\n");
        let (rest, res) = line_comment::<nom::error::Error<Span>>(input).unwrap();
        assert_eq!(rest.fragment(), &"");
        assert_eq!(res.fragment(), input.fragment());
    }

    #[test]
    fn test_block_comment() -> Result<(), Box<dyn Error>> {
        let input = Span::new("/*\n\n*/");
        let (rest, res) = block_comment::<nom::error::Error<Span>>(input)?;
        assert_eq!(rest.fragment(), &"");
        assert_eq!(res.fragment(), input.fragment());
        Ok(())
    }

    #[test]
    fn test_comment_whitespace0() -> Result<(), Box<dyn Error>> {
        let input = Span::new(" ");
        let (rest, res) = comment_whitespace0::<nom::error::Error<Span>>(input)?;
        assert_eq!(rest.fragment(), &"");
        assert_eq!(res.fragment(), input.fragment());
        Ok(())
    }
}
