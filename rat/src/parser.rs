/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use pest::Parser as _;

use std::error::Error;
use std::fmt::Display;
use std::str::FromStr;

use crate::boolean::Boolean;
use crate::decimal::Decimal;
use crate::expression::Expression;
use crate::integer::Integer;
use crate::quote::Quote;
use crate::signal::Signal;
use crate::source::Origin;
use crate::string::String;
use crate::symbol::Symbol;
use crate::vocabulary::Vocabulary;
use crate::word::{OwnedWord, Word};

#[derive(Debug, Default)]
pub struct Parser {
    vocabulary: Vocabulary,
}

impl From<Vocabulary> for Parser {
    fn from(vocabulary: Vocabulary) -> Self {
        Self { vocabulary }
    }
}

impl Parser {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_prelude() -> Self {
        Self {
            vocabulary: Vocabulary::with_prelude(),
        }
    }

    pub fn parse(
        &mut self,
        origin: impl AsRef<Origin>,
        source: &str,
    ) -> Result<Vec<Expression>, ParseError> {
        let origin = origin.as_ref();
        let mut program = Vec::new();
        let pairs = Grammar::parse(Rule::Program, source).map_err(with_origin(origin))?;

        for pair in pairs {
            match pair.as_rule() {
                Rule::Definition => {
                    let (word, definition) = parse_definition(&mut self.vocabulary, origin, pair)?;

                    self.vocabulary.define(word.into(), definition);
                }
                Rule::Word => {
                    let span = pair.as_span();
                    let word = parse_word(origin, pair)?;
                    let definition = self
                        .vocabulary
                        .lookup(word)
                        .ok_or_else(|| parse_error(origin, span, UNDEFINED_WORD))?;

                    program.extend_from_slice(definition);
                }
                Rule::Expression => {
                    let expression = parse_expression(&mut self.vocabulary, origin, pair)?;
                    program.push(expression);
                }
                Rule::EOI => (),
                rule => unreachable!("unexpected rule: `{rule:?}`"),
            }
        }

        Ok(program)
    }
}

impl FromStr for OwnedWord {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Word, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_word(Origin::Unknown, pairs.next().unwrap()).map(ToOwned::to_owned)
    }
}

impl FromStr for Boolean {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Boolean, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_boolean(Origin::Unknown, pairs.next().unwrap())
    }
}

impl FromStr for Decimal {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Decimal, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_decimal(Origin::Unknown, pairs.next().unwrap())
    }
}

impl FromStr for Integer {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Integer, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_integer(Origin::Unknown, pairs.next().unwrap())
    }
}

impl FromStr for Quote {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Quote, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_quote(
            &mut Default::default(),
            Origin::Unknown,
            pairs.next().unwrap(),
        )
    }
}

impl FromStr for Signal {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Signal, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_signal(pairs.next().unwrap())
    }
}

impl FromStr for String {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::String, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_string(Origin::Unknown, pairs.next().unwrap())
    }
}

impl FromStr for Symbol {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Symbol, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_symbol(Origin::Unknown, pairs.next().unwrap())
    }
}

#[derive(Debug)]
pub struct ParseError {
    error: Box<PestError>,
}

const _: [(); 8] = [(); std::mem::size_of::<ParseError>()];

impl Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.error)
    }
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.error.source()
    }
}

#[derive(Parser)]
#[grammar = "src/grammar.pest"]
struct Grammar;

type PestSpan<'a> = pest::Span<'a>;
type PestPair<'a> = pest::iterators::Pair<'a, Rule>;
type PestError = pest::error::Error<Rule>;
type PestErrorVariant = pest::error::ErrorVariant<Rule>;

struct PestErrorWithOrigin(PestError);

fn with_origin(origin: impl AsRef<Origin>) -> impl Fn(PestError) -> PestErrorWithOrigin {
    move |e| PestErrorWithOrigin(e.with_path(origin.as_ref().as_str()))
}

impl From<PestErrorWithOrigin> for ParseError {
    fn from(PestErrorWithOrigin(error): PestErrorWithOrigin) -> Self {
        let error = error.into();
        Self { error }
    }
}

fn parse_error(origin: impl AsRef<Origin>, span: PestSpan, message: impl Display) -> ParseError {
    ParseError {
        error: PestError::new_from_span(
            PestErrorVariant::CustomError {
                message: message.to_string(),
            },
            span,
        )
        .with_path(origin.as_ref().as_str())
        .into(),
    }
}

fn parse_definition<'a>(
    vocabulary: &mut Vocabulary,
    origin: impl AsRef<Origin>,
    pair: PestPair<'a>,
) -> Result<(&'a Word, Box<[Expression]>), ParseError> {
    assert_eq!(pair.as_rule(), Rule::Definition);

    let mut pairs = pair.into_inner();
    assert_eq!(Rule::Colon, pairs.next().unwrap().as_rule());

    let word = pairs
        .next()
        .map(|p| parse_word(origin.as_ref(), p))
        .unwrap()?;

    let mut definition = Vec::new();
    for pair in pairs {
        match pair.as_rule() {
            Rule::Word => {
                let span = pair.as_span();
                let word = parse_word(origin.as_ref(), pair)?;
                let expression = vocabulary
                    .lookup(word)
                    .ok_or_else(|| parse_error(origin.as_ref(), span, UNDEFINED_WORD))?;

                definition.extend(expression.iter().cloned())
            }
            Rule::Expression => {
                let expression = parse_expression(vocabulary, origin.as_ref(), pair)?;
                definition.push(expression);
            }
            Rule::Semicolon => (),
            rule => unreachable!("unexpected rule: `{rule:?}`"),
        }
    }

    Ok((word, definition.into_boxed_slice()))
}

fn parse_expression(
    vocabulary: &mut Vocabulary,
    origin: impl AsRef<Origin>,
    pair: PestPair,
) -> Result<Expression, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Expression);
    let pair = pair.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::Boolean => parse_boolean(origin, pair).map(Expression::Boolean),
        Rule::Decimal => parse_decimal(origin, pair).map(Expression::Decimal),
        Rule::Integer => parse_integer(origin, pair).map(Expression::Integer),
        Rule::Quote => parse_quote(vocabulary, origin, pair).map(Expression::Quote),
        Rule::Signal => parse_signal(pair).map(Expression::Signal),
        Rule::String => parse_string(origin, pair).map(Expression::String),
        Rule::Symbol => parse_symbol(origin, pair).map(Expression::Symbol),
        rule => unreachable!("unexpected rule: `{rule:?}`"),
    }
}

fn parse_word(origin: impl AsRef<Origin>, pair: PestPair) -> Result<&Word, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Word);
    Word::try_from_literal(pair.as_str()).map_err(|e| parse_error(origin, pair.as_span(), e))
}

fn parse_boolean(_: impl AsRef<Origin>, pair: PestPair) -> Result<Boolean, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Boolean);
    match pair.as_str() {
        "⊥" => Ok(Boolean(false)),
        "⊤" => Ok(Boolean(true)),
        literal => unreachable!("unexpected literal for boolean: `{literal}`"),
    }
}

fn parse_decimal(origin: impl AsRef<Origin>, pair: PestPair) -> Result<Decimal, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Decimal);
    match pair.as_str() {
        "-∞" => Ok(Decimal::NEG_INFINITY),
        "+∞" => Ok(Decimal::INFINITY),
        "∞" => Ok(Decimal::INFINITY),
        "0.NaN" => Ok(Decimal::NAN),
        literal => literal
            .parse()
            .map(Decimal)
            .map_err(|e| parse_error(origin, pair.as_span(), e)),
    }
}

fn parse_integer(origin: impl AsRef<Origin>, pair: PestPair) -> Result<Integer, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Integer);
    pair.as_str()
        .parse()
        .map(Integer)
        .map_err(|e| parse_error(origin, pair.as_span(), e))
}

fn parse_quote(
    vocabulary: &mut Vocabulary,
    origin: impl AsRef<Origin>,
    pair: PestPair,
) -> Result<Quote, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Quote);
    let mut quote = Quote::new();

    for pair in pair.into_inner() {
        match pair.as_rule() {
            Rule::Word => {
                let span = pair.as_span();
                let word = parse_word(origin.as_ref(), pair)?;
                let definition = vocabulary
                    .lookup(word)
                    .ok_or_else(|| parse_error(origin.as_ref(), span, UNDEFINED_WORD))?;

                quote.extend(definition.iter().cloned())
            }
            Rule::Expression => {
                let expression = parse_expression(vocabulary, origin.as_ref(), pair)?;
                quote.push(expression);
            }
            Rule::LeftSquareBracket | Rule::RightSquareBracket => (),
            rule => unreachable!("unexpected rule: `{rule:?}`"),
        }
    }

    Ok(quote)
}

fn parse_signal(pair: PestPair) -> Result<Signal, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Signal);
    Ok(unsafe { Signal::new(&pair.as_str()[1..]) })
}

fn parse_string(origin: impl AsRef<Origin>, pair: PestPair) -> Result<String, ParseError> {
    assert_eq!(pair.as_rule(), Rule::String);
    pair.into_inner()
        .map(|p| parse_unicode_scalar_value(origin.as_ref(), p))
        .collect()
}

fn parse_symbol(origin: impl AsRef<Origin>, pair: PestPair) -> Result<Symbol, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Symbol);
    pair.into_inner()
        .map(|p| parse_unicode_scalar_value(origin.as_ref(), p))
        .collect()
}

fn parse_unicode_scalar_value(
    origin: impl AsRef<Origin>,
    pair: PestPair,
) -> Result<char, ParseError> {
    assert!(
        Rule::StringUnicodeScalarValue == pair.as_rule()
            || Rule::SymbolUnicodeScalarValue == pair.as_rule()
    );

    match pair.as_str() {
        "\\n" => Ok('\n'),
        "\\r" => Ok('\r'),
        "\\t" => Ok('\t'),
        "\\\\" => Ok('\\'),
        "\\'" => Ok('\''),
        "\\\"" => Ok('"'),
        s => {
            if s.ends_with('}') && s.starts_with("\\u{") {
                return u32::from_str_radix(&s[3..s.len() - 1], 16)
                    .map_err(|e| parse_error(origin.as_ref(), pair.as_span(), e))
                    .and_then(|n| {
                        char::from_u32(n).ok_or_else(|| {
                            parse_error(origin.as_ref(), pair.as_span(), "Invalid character")
                        })
                    });
            }

            s.parse()
                .map_err(|e| parse_error(origin, pair.as_span(), e))
        }
    }
}

fn check_token_boundary(s: &str) -> Result<(), ParseError> {
    const ERROR_MESSAGE: &str = "breaks are not allowed";

    let trimmed = s.trim_start();
    if trimmed.len() < s.len() {
        return Err(parse_error(
            Origin::Unknown,
            PestSpan::new(s, 0, s.len() - trimmed.len()).unwrap(),
            ERROR_MESSAGE,
        ));
    }

    let trimmed = s.trim_end();
    if trimmed.len() < s.len() {
        return Err(parse_error(
            Origin::Unknown,
            PestSpan::new(s, trimmed.len(), s.len()).unwrap(),
            ERROR_MESSAGE,
        ));
    }

    Ok(())
}

const UNDEFINED_WORD: &str = "undefined word";

#[cfg(test)]
mod test {
    use std::borrow::Borrow;

    use crate::boolean::Boolean;
    use crate::decimal::Decimal;
    use crate::expression::Expression;
    use crate::integer::Integer;
    use crate::quote::Quote;
    use crate::signal::{self, Signal};
    use crate::string::String;
    use crate::symbol::Symbol;
    use crate::word::{OwnedWord, Word};

    #[test]
    fn parse_word() {
        assert!(Word::try_from_literal(" ans").is_err());
        assert!(Word::try_from_literal("ans ").is_err());
        assert_eq!(
            Word::try_from_literal("ans").unwrap(),
            "ans".parse::<OwnedWord>().unwrap().borrow()
        );
    }

    #[test]
    fn parse_boolean() {
        assert!(" ⊥".parse::<Boolean>().is_err());
        assert!("⊥ ".parse::<Boolean>().is_err());
        assert_eq!(Boolean(false), "⊥".parse().unwrap());

        assert!(" ⊤".parse::<Boolean>().is_err());
        assert!("⊤ ".parse::<Boolean>().is_err());
        assert_eq!(Boolean(true), "⊤".parse().unwrap());
    }

    #[test]
    fn parse_decimal() {
        assert!(" 3.14".parse::<Decimal>().is_err());
        assert!("3.14 ".parse::<Decimal>().is_err());
        assert_eq!(Decimal(3.14), "3.14".parse().unwrap());
    }

    #[test]
    fn parse_integer() {
        assert!(" 42".parse::<Integer>().is_err());
        assert!("42 ".parse::<Integer>().is_err());
        assert_eq!(Integer(42), "42".parse().unwrap());
    }

    #[test]
    fn parse_quote() {
        assert!(" [⊥ ⊤ 42 3.14 $IoError 'hello' \"world\" []]"
            .parse::<Quote>()
            .is_err());
        assert!("[⊥ ⊤ 42 3.14 $IoError 'hello' \"world\" []] "
            .parse::<Quote>()
            .is_err());
        assert_eq!(
            [
                Expression::Boolean(Boolean(false)),
                Expression::Boolean(Boolean(true)),
                Expression::Integer(Integer(42)),
                Expression::Decimal(Decimal(3.14)),
                Expression::Signal(unsafe { Signal::new("IoError") }),
                Expression::Symbol(Symbol::new("hello")),
                Expression::String(String::from_utf8("world")),
                Expression::Quote(Quote::default()),
            ]
            .into_iter()
            .collect::<Quote>(),
            "[⊥ ⊤ 42 3.14 $IoError 'hello' \"world\" []]"
                .parse::<Quote>()
                .unwrap()
        );
    }

    #[test]
    fn parse_signal() {
        assert!(" $StackUnderflow".parse::<Signal>().is_err());
        assert!("$StackUnderflow ".parse::<Signal>().is_err());
        assert_eq!(
            signal::stack_underflow(),
            "$StackUnderflow".parse().unwrap()
        );
    }

    #[test]
    fn parse_string() {
        assert!(" \"hello\"".parse::<String>().is_err());
        assert!("\"hello\" ".parse::<String>().is_err());
        assert_eq!(
            String::from_iter("hello".chars()),
            "\"hello\"".parse().unwrap()
        );

        assert_eq!(
            String::from_iter("a\"a".chars()),
            "\"a\\\"a\"".parse().unwrap()
        );

        assert_eq!(String::from_iter("a'a".chars()), "\"a'a\"".parse().unwrap());
    }

    #[test]
    fn parse_symbol() {
        assert!(" 'hello'".parse::<Symbol>().is_err());
        assert!("'hello' ".parse::<Symbol>().is_err());
        assert_eq!(
            Symbol::from_iter("hello".chars()),
            "'hello'".parse().unwrap()
        );

        assert_eq!(Symbol::from_iter("a\"a".chars()), "'a\"a'".parse().unwrap());
        assert_eq!(Symbol::from_iter("a'a".chars()), "'a\\'a'".parse().unwrap());
    }
}
