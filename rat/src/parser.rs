/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use pest::Parser as _;

use std::collections::HashMap;
use std::error::Error;
use std::fmt::Display;
use std::path::Path;
use std::str::FromStr;
use std::string::String as StdString;
use std::sync::Arc;
use std::{env, fs};

use crate::boolean::Boolean;
use crate::decimal::Decimal;
use crate::expression::Expression;
use crate::integer::Integer;
use crate::locution::{Locution, OwnedLocution};
use crate::quote::Quote;
use crate::signal::Signal;
use crate::string::String;
use crate::symbol::Symbol;
use crate::vocabulary::{Definition, Visibility, Vocabulary};
use crate::word::{OwnedWord, Word};

#[derive(Debug, Default)]
pub struct Parser {
    vocabulary: Vocabulary,
    cache: HashMap<OwnedLocution, Arc<Vocabulary>>,
}

impl From<Vocabulary> for Parser {
    fn from(vocabulary: Vocabulary) -> Self {
        Self {
            vocabulary,
            cache: Default::default(),
        }
    }
}

impl Parser {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_prelude() -> Self {
        Self {
            vocabulary: Vocabulary::with_prelude(),
            cache: Default::default(),
        }
    }

    pub fn vocabulary(&self) -> &Vocabulary {
        &self.vocabulary
    }

    pub fn parse(&mut self, origin: Origin, source: &str) -> Result<Vec<Expression>, ParseError> {
        let pairs = Grammar::parse(Rule::Program, source).map_err(with_origin(origin))?;
        let mut program = Vec::new();

        for pair in pairs {
            match pair.as_rule() {
                Rule::Definition => parse_definition(self, origin, pair)?,
                Rule::Phrase => {
                    let phrase = parse_phrase(self, origin, pair)?;
                    program.extend(phrase.into_iter());
                }
                Rule::EOI => break,
                rule => unreachable!("unexpected rule: `{rule:?}`"),
            }
        }

        Ok(program)
    }

    fn import(
        &mut self,
        word: &Word,
        locution: &Locution,
        visibility: Visibility,
    ) -> Result<(), ImportError> {
        if let Some(vocabulary) = self.cache.get(locution) {
            self.vocabulary.define(
                word.to_owned(),
                Definition::Vocabulary {
                    vocabulary: vocabulary.clone(),
                    visibility,
                },
            );

            return Ok(());
        }

        let mut words = locution.words();

        let mut path = if locution.as_str().starts_with("rat\\") {
            words.next();
            crate::home_dir().join("lib")
        } else {
            env::current_dir()
                .map_err(|error| ImportError::new(format!("`{}` {}", locution, error)))?
        };

        for word in words {
            if !path.is_dir() {
                return Err(ImportError::new(format!(
                    "`{}` {} is not a directory",
                    locution,
                    path.display()
                )));
            }

            path.push(word.as_str());
        }

        path.set_extension("rat");

        if !path.is_file() {
            return Err(ImportError::new(format!(
                "`{}` {} is not a regular file",
                locution,
                path.display()
            )));
        }

        let source = fs::read_to_string(&path)
            .map_err(|e| ImportError::new(format!("`{}` {} {}", locution, path.display(), e)))?;

        let mut parser = Parser::with_prelude();

        parser
            .parse(Origin::Path(path.as_path()), &source)
            .map_err(|e| ImportError::new(format!("`{}`\n{}", locution, e)))?;

        parser.vocabulary.retain(|_, d| d.is_extern());

        let vocabulary = Arc::new(parser.vocabulary);

        self.cache.insert(locution.to_owned(), vocabulary.clone());
        self.vocabulary.define(
            word.to_owned(),
            Definition::Vocabulary {
                vocabulary,
                visibility,
            },
        );

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Origin<'a> {
    Path(&'a Path),
    Unknown,
}

const _: [(); 16] = [(); std::mem::size_of::<Origin>()];

impl<'a> Origin<'a> {
    pub fn display(&self) -> impl Display + '_ {
        self
    }
}

impl<'a> Display for Origin<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Origin::Path(path) => path.display().fmt(f),
            Origin::Unknown => write!(f, "<unknown>"),
        }
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

impl FromStr for OwnedLocution {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Locution, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_locution(Origin::Unknown, pairs.next().unwrap()).map(ToOwned::to_owned)
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

#[derive(Debug)]
pub struct ImportError {
    message: Box<str>,
}

impl ImportError {
    fn new(message: StdString) -> Self {
        Self {
            message: message.into(),
        }
    }
}

const _: [(); 16] = [(); std::mem::size_of::<ImportError>()];

impl Display for ImportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "unable to import: {}", self.message)
    }
}

impl Error for ImportError {}

#[derive(Parser)]
#[grammar = "src/grammar.pest"]
struct Grammar;

type PestSpan<'a> = pest::Span<'a>;
type PestPair<'a> = pest::iterators::Pair<'a, Rule>;
type PestError = pest::error::Error<Rule>;
type PestErrorVariant = pest::error::ErrorVariant<Rule>;

struct PestErrorWithOrigin(PestError);

fn with_origin(origin: Origin) -> impl Fn(PestError) -> PestErrorWithOrigin + '_ {
    let path = origin.display().to_string();
    move |e| PestErrorWithOrigin(e.with_path(&path))
}

impl From<PestErrorWithOrigin> for ParseError {
    fn from(PestErrorWithOrigin(error): PestErrorWithOrigin) -> Self {
        let error = error.into();
        Self { error }
    }
}

fn parse_error(origin: Origin, span: PestSpan, message: impl Display) -> ParseError {
    with_origin(origin)(PestError::new_from_span(
        PestErrorVariant::CustomError {
            message: message.to_string(),
        },
        span,
    ))
    .into()
}

fn parse_definition(parser: &mut Parser, origin: Origin, pair: PestPair) -> Result<(), ParseError> {
    assert_eq!(pair.as_rule(), Rule::Definition);
    let span = pair.as_span();
    let mut pairs = pair.into_inner();

    let visibility = match pairs.next().unwrap().as_rule() {
        Rule::Division => Visibility::Extern,
        Rule::Colon => Visibility::Intern,
        rule => unreachable!("unexpected rule: `{rule:?}`"),
    };

    let word = pairs.next().map(|p| parse_word(origin, p)).unwrap()?;

    match pairs.next().unwrap().as_rule() {
        Rule::At => {
            let locution = parse_locution(origin, pairs.next().unwrap())?;

            parser
                .import(word, locution, visibility)
                .map_err(|e| parse_error(origin, span, e))
        }
        Rule::LeftArrow => {
            let phrase = parse_phrase(parser, origin, pairs.next().unwrap())?;

            parser.vocabulary.define(
                word.to_owned(),
                Definition::Phrase {
                    phrase: phrase.into(),
                    visibility,
                },
            );

            Ok(())
        }
        rule => unreachable!("unexpected rule: `{rule:?}`"),
    }
}

fn parse_word<'a>(origin: Origin, pair: PestPair<'a>) -> Result<&'a Word, ParseError> {
    assert!(matches!(pair.as_rule(), Rule::Word | Rule::_Word));
    Word::try_from_literal(pair.as_str()).map_err(|e| parse_error(origin, pair.as_span(), e))
}

fn parse_locution<'a>(origin: Origin, pair: PestPair<'a>) -> Result<&'a Locution, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Locution);
    Locution::try_from_literal(pair.as_str()).map_err(|e| parse_error(origin, pair.as_span(), e))
}

fn parse_expression(
    parser: &mut Parser,
    origin: Origin,
    pair: PestPair,
) -> Result<Expression, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Expression);
    let pair = pair.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::Boolean => parse_boolean(origin, pair).map(Expression::Boolean),
        Rule::Decimal => parse_decimal(origin, pair).map(Expression::Decimal),
        Rule::Integer => parse_integer(origin, pair).map(Expression::Integer),
        Rule::Quote => parse_quote(parser, origin, pair).map(Expression::Quote),
        Rule::Signal => parse_signal(pair).map(Expression::Signal),
        Rule::String => parse_string(origin, pair).map(Expression::String),
        Rule::Symbol => parse_symbol(origin, pair).map(Expression::Symbol),
        rule => unreachable!("unexpected rule: `{rule:?}`"),
    }
}

fn parse_phrase(
    parser: &mut Parser,
    origin: Origin,
    pair: PestPair,
) -> Result<Vec<Expression>, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Phrase);
    let mut phrase = Vec::new();

    for pair in pair.into_inner() {
        match pair.as_rule() {
            Rule::Locution => {
                let span = pair.as_span();
                let locution = parse_locution(origin, pair)?;
                parser
                    .vocabulary
                    .lookup(locution)
                    .map(|expressions| phrase.extend_from_slice(expressions))
                    .ok_or_else(|| parse_error(origin, span, undefined_locution(locution)))?;
            }
            Rule::Expression => {
                let expression = parse_expression(parser, origin, pair)?;
                phrase.push(expression);
            }
            rule => unreachable!("unexpected rule: `{rule:?}`"),
        }
    }

    Ok(phrase)
}

fn parse_boolean(_: Origin, pair: PestPair) -> Result<Boolean, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Boolean);
    match pair.as_str() {
        "⊥" => Ok(Boolean(false)),
        "⊤" => Ok(Boolean(true)),
        literal => unreachable!("unexpected literal for boolean: `{literal}`"),
    }
}

fn parse_decimal(origin: Origin, pair: PestPair) -> Result<Decimal, ParseError> {
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

fn parse_integer(origin: Origin, pair: PestPair) -> Result<Integer, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Integer);
    pair.as_str()
        .parse()
        .map(Integer)
        .map_err(|e| parse_error(origin, pair.as_span(), e))
}

fn parse_quote(parser: &mut Parser, origin: Origin, pair: PestPair) -> Result<Quote, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Quote);
    let mut quote = Quote::new();

    for pair in pair.into_inner() {
        match pair.as_rule() {
            Rule::Phrase => {
                let phrase = parse_phrase(parser, origin, pair)?;
                quote.extend(phrase.into_iter());
            }
            Rule::LeftSquareBracket => (),
            Rule::RightSquareBracket => break,
            rule => unreachable!("unexpected rule: `{rule:?}`"),
        }
    }

    Ok(quote)
}

fn parse_signal(pair: PestPair) -> Result<Signal, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Signal);
    Ok(unsafe { Signal::new(&pair.as_str()[1..]) })
}

fn parse_string(origin: Origin, pair: PestPair) -> Result<String, ParseError> {
    assert_eq!(pair.as_rule(), Rule::String);
    pair.into_inner()
        .map(|p| parse_unicode_scalar_value(origin, p))
        .collect()
}

fn parse_symbol(origin: Origin, pair: PestPair) -> Result<Symbol, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Symbol);
    pair.into_inner()
        .map(|p| parse_unicode_scalar_value(origin, p))
        .collect()
}

fn parse_unicode_scalar_value(origin: Origin, pair: PestPair) -> Result<char, ParseError> {
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
                    .map_err(|e| parse_error(origin, pair.as_span(), e))
                    .and_then(|n| {
                        char::from_u32(n)
                            .ok_or_else(|| parse_error(origin, pair.as_span(), "Invalid character"))
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

fn undefined_locution(locution: &Locution) -> StdString {
    format!("undefined locution: `{locution}`")
}

#[cfg(test)]
mod test {
    use std::borrow::Borrow;

    use crate::boolean::Boolean;
    use crate::decimal::Decimal;
    use crate::expression::Expression;
    use crate::integer::Integer;
    use crate::locution::{Locution, OwnedLocution};
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
    fn parse_locution() {
        assert!(Locution::try_from_literal(" math\\abs").is_err());
        assert!(Locution::try_from_literal("math\\abs ").is_err());
        assert!(Locution::try_from_literal("math\\").is_err());
        assert!(Locution::try_from_literal("\\abs").is_err());
        assert_eq!(
            Locution::try_from_literal("math\\abs").unwrap(),
            "math\\abs".parse::<OwnedLocution>().unwrap().borrow()
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
