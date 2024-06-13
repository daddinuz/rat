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
use crate::dictionary::{Definition, Dictionary, Visibility};
use crate::expression::Expression;
use crate::identifier::{Identifier, OwnedIdentifier};
use crate::integer::Integer;
use crate::quote::Quote;
use crate::string::String;
use crate::symbol::Symbol;
use crate::word::{OwnedWord, Word};

#[derive(Debug, Default)]
pub struct Parser {
    dictionary: Dictionary,
    cache: HashMap<OwnedIdentifier, Arc<Dictionary>>,
}

impl From<Dictionary> for Parser {
    fn from(dictionary: Dictionary) -> Self {
        Self {
            dictionary,
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
            dictionary: Dictionary::with_prelude(),
            cache: Default::default(),
        }
    }

    pub fn dictionary(&self) -> &Dictionary {
        &self.dictionary
    }

    pub fn parse(&mut self, origin: Origin, source: &str) -> Result<Vec<Expression>, ParseError> {
        let pairs = Grammar::parse(Rule::Program, source).map_err(with_origin(origin))?;
        let mut program = Vec::new();

        for pair in pairs {
            match pair.as_rule() {
                Rule::Statement => parse_statement(self, origin, pair)?,
                Rule::Expression => parse_expressions(self, origin, pair, &mut program)?,
                Rule::EOI => break,
                rule => unreachable!("unexpected rule: `{rule:?}`"),
            }
        }

        Ok(program)
    }

    fn import(
        &mut self,
        word: &Word,
        identifier: &Identifier,
        visibility: Visibility,
    ) -> Result<(), ImportError> {
        if let Some(dictionary) = self.cache.get(identifier) {
            self.dictionary.define(
                word.to_owned(),
                Definition::Dictionary {
                    dictionary: dictionary.clone(),
                    visibility,
                },
            );

            return Ok(());
        }

        let mut words = identifier.words();

        let mut path = if identifier.as_str().starts_with("rat/") {
            words.next();
            crate::home_dir().join("lib")
        } else {
            env::current_dir()
                .map_err(|error| ImportError::new(format!("`{}` {}", identifier, error)))?
        };

        for word in words {
            if !path.is_dir() {
                return Err(ImportError::new(format!(
                    "`{}` {} is not a directory",
                    identifier,
                    path.display()
                )));
            }

            path.push(word.as_str());
        }

        path.set_extension("rat");

        if !path.is_file() {
            return Err(ImportError::new(format!(
                "`{}` {} is not a regular file",
                identifier,
                path.display()
            )));
        }

        let source = fs::read_to_string(&path)
            .map_err(|e| ImportError::new(format!("`{}` {} {}", identifier, path.display(), e)))?;

        let mut parser = Parser::with_prelude();

        parser
            .parse(Origin::Path(path.as_path()), &source)
            .map_err(|e| ImportError::new(format!("`{}`\n{}", identifier, e)))?;

        parser.dictionary.retain(|_, d| d.is_extern());

        let dictionary = Arc::new(parser.dictionary);

        self.cache.insert(identifier.to_owned(), dictionary.clone());
        self.dictionary.define(
            word.to_owned(),
            Definition::Dictionary {
                dictionary,
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

impl FromStr for OwnedIdentifier {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs =
            Grammar::parse(Rule::Identifier, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_identifier(Origin::Unknown, pairs.next().unwrap()).map(ToOwned::to_owned)
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

fn parse_statement(parser: &mut Parser, origin: Origin, pair: PestPair) -> Result<(), ParseError> {
    assert_eq!(pair.as_rule(), Rule::Statement);
    let pair = pair.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::Define => parse_define(parser, origin, pair),
        Rule::Import => parse_import(parser, origin, pair),
        rule => unreachable!("unexpected rule: `{rule:?}`"),
    }
}

fn parse_define(parser: &mut Parser, origin: Origin, pair: PestPair) -> Result<(), ParseError> {
    assert_eq!(pair.as_rule(), Rule::Define);
    let mut pairs = pair.into_inner().peekable();

    let visibility = match pairs.peek().unwrap().as_rule() {
        Rule::Export => {
            pairs.next().unwrap();
            Visibility::Extern
        }
        _ => Visibility::Intern,
    };

    let word = pairs.next().map(|p| parse_word(origin, p)).unwrap()?;
    let mut expressions = Vec::new();
    pairs.try_for_each(|p| parse_expressions(parser, origin, p, &mut expressions))?;

    parser.dictionary.define(
        word.to_owned(),
        Definition::Body {
            body: expressions.into(),
            visibility,
        },
    );

    Ok(())
}

fn parse_import(parser: &mut Parser, origin: Origin, pair: PestPair) -> Result<(), ParseError> {
    assert_eq!(pair.as_rule(), Rule::Import);
    let span = pair.as_span();
    let mut pairs = pair.into_inner().peekable();

    let visibility = match pairs.peek().unwrap().as_rule() {
        Rule::Export => {
            pairs.next().unwrap();
            Visibility::Extern
        }
        _ => Visibility::Intern,
    };

    let word = pairs.next().map(|p| parse_word(origin, p)).unwrap()?;
    let identifier = parse_identifier(origin, pairs.next().unwrap())?;

    parser
        .import(word, identifier, visibility)
        .map_err(|e| parse_error(origin, span, e))
}

fn parse_word<'a>(origin: Origin, pair: PestPair<'a>) -> Result<&'a Word, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Word);
    Word::try_from_literal(pair.as_str()).map_err(|e| parse_error(origin, pair.as_span(), e))
}

fn parse_identifier<'a>(origin: Origin, pair: PestPair<'a>) -> Result<&'a Identifier, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Identifier);
    Identifier::try_from_literal(pair.as_str()).map_err(|e| parse_error(origin, pair.as_span(), e))
}

fn parse_expressions(
    parser: &mut Parser,
    origin: Origin,
    pair: PestPair,
    buf: &mut Vec<Expression>,
) -> Result<(), ParseError> {
    assert_eq!(pair.as_rule(), Rule::Expression);
    let pair = pair.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::Boolean => parse_boolean(origin, pair).map(|e| buf.push(Expression::Boolean(e))),
        Rule::Decimal => parse_decimal(origin, pair).map(|e| buf.push(Expression::Decimal(e))),
        Rule::Integer => parse_integer(origin, pair).map(|e| buf.push(Expression::Integer(e))),
        Rule::Quote => parse_quote(parser, origin, pair).map(|e| buf.push(Expression::Quote(e))),
        Rule::String => parse_string(origin, pair).map(|e| buf.push(Expression::String(e))),
        Rule::Symbol => parse_symbol(origin, pair).map(|e| buf.push(Expression::Symbol(e))),
        Rule::Identifier => {
            let span = pair.as_span();
            let identifier = parse_identifier(origin, pair)?;
            parser
                .dictionary
                .lookup(identifier)
                .map(|expressions| buf.extend_from_slice(expressions))
                .ok_or_else(|| parse_error(origin, span, undefined_identifier(identifier)))
        }
        rule => unreachable!("unexpected rule: `{rule:?}`"),
    }
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
    let mut expressions = Vec::new();
    pair.into_inner()
        .try_for_each(|pair| parse_expressions(parser, origin, pair, &mut expressions))?;

    Ok(expressions.into_iter().collect())
}

fn parse_string(origin: Origin, pair: PestPair) -> Result<String, ParseError> {
    assert_eq!(pair.as_rule(), Rule::String);
    pair.into_inner()
        .map(|p| parse_unicode_scalar_value(origin, p))
        .collect()
}

fn parse_symbol(origin: Origin, pair: PestPair) -> Result<Symbol, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Symbol);
    let pair = pair.into_inner().next().unwrap();
    match pair.as_rule() {
        Rule::Identifier => Ok(pair.as_str().chars().collect()),
        Rule::String => pair
            .into_inner()
            .map(|p| parse_unicode_scalar_value(origin, p))
            .collect(),
        rule => unreachable!("unexpected rule: `{rule:?}`"),
    }
}

fn parse_unicode_scalar_value(origin: Origin, pair: PestPair) -> Result<char, ParseError> {
    assert_eq!(pair.as_rule(), Rule::UnicodeScalarValue);

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

fn undefined_identifier(identifier: &Identifier) -> StdString {
    format!("undefined identifier: `{identifier}`")
}

#[cfg(test)]
mod test {
    use std::borrow::Borrow;

    use crate::boolean::Boolean;
    use crate::decimal::Decimal;
    use crate::expression::Expression;
    use crate::identifier::{Identifier, OwnedIdentifier};
    use crate::integer::Integer;
    use crate::quote::Quote;
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
    fn parse_identifier() {
        assert!(Identifier::try_from_literal(" math/abs").is_err());
        assert!(Identifier::try_from_literal("math/abs ").is_err());
        assert!(Identifier::try_from_literal("math/").is_err());
        assert!(Identifier::try_from_literal("/abs").is_err());
        assert_eq!(
            Identifier::try_from_literal("math/abs").unwrap(),
            "math/abs".parse::<OwnedIdentifier>().unwrap().borrow()
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
        assert!(" [⊥ ⊤ 42 3.14 $hello \"world\" []]"
            .parse::<Quote>()
            .is_err());
        assert!("[⊥ ⊤ 42 3.14 $hello \"world\" []] "
            .parse::<Quote>()
            .is_err());
        assert_eq!(
            [
                Expression::Boolean(Boolean(false)),
                Expression::Boolean(Boolean(true)),
                Expression::Integer(Integer(42)),
                Expression::Decimal(Decimal(3.14)),
                Expression::Symbol(Symbol::new("hello")),
                Expression::String(String::from_utf8("world")),
                Expression::Quote(Quote::default()),
            ]
            .into_iter()
            .collect::<Quote>(),
            "[⊥ ⊤ 42 3.14 $hello \"world\" []]"
                .parse::<Quote>()
                .unwrap()
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
        assert!(" $hello".parse::<Symbol>().is_err());
        assert!("$hello ".parse::<Symbol>().is_err());
        assert!(" $\"hello\"".parse::<Symbol>().is_err());
        assert!("$\"hello\" ".parse::<Symbol>().is_err());
        assert_eq!(
            Symbol::from_iter("hello".chars()),
            "$hello".parse().unwrap()
        );

        assert_eq!(
            Symbol::from_iter("a\tstring".chars()),
            "$\"a\tstring\"".parse().unwrap()
        );
        assert_eq!(
            Symbol::from_iter("a\tstring".chars()),
            r#"$"a\tstring""#.parse().unwrap()
        );
    }
}
