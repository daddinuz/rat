/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use hashbrown::HashMap;
use pest::Parser as _;
use pest_derive::Parser;

use std::error::Error;
use std::fmt::Display;
use std::path::Path;
use std::str::FromStr;
use std::string::String as StdString;
use std::sync::Arc;
use std::{env, fs};

use crate::boolean::Boolean;
use crate::character::Character;
use crate::component::{Component, OwnedComponent};
use crate::decimal::Decimal;
use crate::definition::Definition;
use crate::dictionary::Dictionary;
use crate::identifier::{Identifier, OwnedIdentifier};
use crate::integer::Integer;
use crate::object::Object;
use crate::quote::Quote;
use crate::string::String;
use crate::symbol::Symbol;
use crate::visibility::Visibility;
use crate::word::Word;

#[derive(Clone, Debug, Default)]
pub struct Parser {
    dictionary: Dictionary,
    prelude: Arc<Dictionary>,
    cache: HashMap<OwnedIdentifier, Arc<Dictionary>>,
}

impl Parser {
    pub fn new(prelude: Arc<Dictionary>) -> Self {
        Self {
            dictionary: Dictionary::new(),
            cache: HashMap::new(),
            prelude,
        }
    }

    pub fn dictionary(&self) -> &Dictionary {
        &self.dictionary
    }

    pub fn prelude(&self) -> &Dictionary {
        &self.prelude
    }

    pub fn parse(&mut self, origin: Origin, source: &str) -> Result<Vec<Word>, ParseError> {
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
        visibility: Visibility,
        component: &Component,
        identifier: &Identifier,
    ) -> Result<(), ImportError> {
        if let Some(dictionary) = self.cache.get(identifier) {
            self.dictionary.insert(
                component.to_owned(),
                Definition::new_dictionary(dictionary.clone(), visibility),
            );

            return Ok(());
        }

        let mut components = identifier.components();

        let mut path = if identifier.as_str().starts_with("rat/") {
            components.next();
            crate::stdlib_dir().to_path_buf()
        } else {
            env::current_dir()
                .map_err(|error| ImportError::new(format!("`{identifier:?}` {error}")))?
        };

        for component in components {
            if !path.is_dir() {
                return Err(ImportError::new(format!(
                    "`{:?}` {} is not a directory",
                    identifier,
                    path.display()
                )));
            }

            path.push(component.as_str());
        }

        path.set_extension("rat");

        if !path.is_file() {
            return Err(ImportError::new(format!(
                "`{:?}` {} is not a regular file",
                identifier,
                path.display()
            )));
        }

        let source = fs::read_to_string(&path).map_err(|e| {
            ImportError::new(format!("`{:?}` {} {}", identifier, path.display(), e))
        })?;

        let mut parser = Parser::new(self.prelude.clone());

        parser
            .parse(Origin::Path(path.as_path()), &source)
            .map_err(|e| ImportError::new(format!("`{identifier:?}`\n{e}")))?;

        parser
            .dictionary
            .retain(|_, d| d.visibility() == Visibility::Extern);

        let dictionary = Arc::new(parser.dictionary);

        self.cache.insert(identifier.to_owned(), dictionary.clone());
        self.dictionary.insert(
            component.to_owned(),
            Definition::new_dictionary(dictionary, visibility),
        );

        Ok(())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Origin<'a> {
    Path(&'a Path),
    Unknown,
}

const _: [(); 2 * std::mem::size_of::<usize>()] = [(); std::mem::size_of::<Origin>()];

impl Origin<'_> {
    pub fn display(&self) -> impl Display {
        self
    }
}

impl Display for Origin<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Origin::Path(path) => path.display().fmt(f),
            Origin::Unknown => write!(f, "<unknown>"),
        }
    }
}

impl FromStr for OwnedComponent {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Component, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_component(Origin::Unknown, pairs.next().unwrap()).map(ToOwned::to_owned)
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

impl FromStr for Character {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        check_token_boundary(s)?;

        let mut pairs = Grammar::parse(Rule::Character, s).map_err(with_origin(Origin::Unknown))?;
        assert_eq!(pairs.len(), 1);

        parse_character(Origin::Unknown, pairs.next().unwrap())
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

const _: [(); std::mem::size_of::<usize>()] = [(); std::mem::size_of::<ParseError>()];

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

const _: [(); 2 * std::mem::size_of::<usize>()] = [(); std::mem::size_of::<ImportError>()];

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

fn with_origin(origin: Origin<'_>) -> impl Fn(PestError) -> PestErrorWithOrigin + '_ {
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
        Rule::DefineStatement => parse_define_statement(parser, origin, pair),
        Rule::ImportStatement => parse_import_statement(parser, origin, pair),
        rule => unreachable!("unexpected rule: `{rule:?}`"),
    }
}

fn parse_define_statement(
    parser: &mut Parser,
    origin: Origin,
    pair: PestPair,
) -> Result<(), ParseError> {
    assert_eq!(pair.as_rule(), Rule::DefineStatement);
    let mut pairs = pair.into_inner().peekable();

    let visibility = match pairs.peek().unwrap().as_rule() {
        Rule::Export => {
            pairs.next().unwrap();
            Visibility::Extern
        }
        _ => Visibility::Intern,
    };

    let component = pairs.next().map(|p| parse_component(origin, p)).unwrap()?;
    let mut words = Vec::new();
    pairs.try_for_each(|p| parse_expressions(parser, origin, p, &mut words))?;

    parser.dictionary.insert(
        component.to_owned(),
        Definition::new_expression(words.into(), visibility),
    );

    Ok(())
}

fn parse_import_statement(
    parser: &mut Parser,
    origin: Origin,
    pair: PestPair,
) -> Result<(), ParseError> {
    assert_eq!(pair.as_rule(), Rule::ImportStatement);
    let span = pair.as_span();
    let mut pairs = pair.into_inner().peekable();

    let visibility = match pairs.peek().unwrap().as_rule() {
        Rule::Export => {
            pairs.next().unwrap();
            Visibility::Extern
        }
        _ => Visibility::Intern,
    };

    let component = pairs.next().map(|p| parse_component(origin, p)).unwrap()?;
    let identifier = parse_identifier(origin, pairs.next().unwrap())?;

    parser
        .import(visibility, component, identifier)
        .map_err(|e| parse_error(origin, span, e))
}

fn parse_component<'a>(origin: Origin, pair: PestPair<'a>) -> Result<&'a Component, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Component);
    Component::try_from_literal(pair.as_str())
        .ok_or_else(|| parse_error(origin, pair.as_span(), "InvalidComponent"))
}

fn parse_identifier<'a>(origin: Origin, pair: PestPair<'a>) -> Result<&'a Identifier, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Identifier);
    Identifier::try_from_literal(pair.as_str())
        .ok_or_else(|| parse_error(origin, pair.as_span(), "InvalidIdentifier"))
}

fn parse_expressions(
    parser: &mut Parser,
    origin: Origin,
    pair: PestPair,
    buf: &mut Vec<Word>,
) -> Result<(), ParseError> {
    assert_eq!(pair.as_rule(), Rule::Expression);
    let pair = pair.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::Boolean => parse_boolean(origin, pair).map(|e| buf.push(Word::Boolean(e))),
        Rule::Decimal => parse_decimal(origin, pair).map(|e| buf.push(Word::Decimal(e))),
        Rule::Integer => parse_integer(origin, pair).map(|e| buf.push(Word::Integer(e))),
        Rule::Character => parse_character(origin, pair).map(|e| buf.push(Word::Character(e))),
        Rule::Quote => {
            parse_quote(parser, origin, pair).map(|e| buf.push(Word::Object(Object::new(e))))
        }
        Rule::String => parse_string(origin, pair).map(|e| buf.push(Word::Object(Object::new(e)))),
        Rule::Symbol => parse_symbol(origin, pair).map(|e| buf.push(Word::Symbol(e))),
        Rule::Identifier => {
            let span = pair.as_span();
            let identifier = parse_identifier(origin, pair)?;
            parser
                .dictionary
                .lookup(identifier)
                .or_else(|| parser.prelude.lookup(identifier))
                .map(|words| buf.extend_from_slice(words))
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
        "-∞" => Ok(-Decimal::INFINITY),
        "+∞" => Ok(Decimal::INFINITY),
        "∞" => Ok(Decimal::INFINITY),
        "+%" => Ok(Decimal::NAN),
        "-%" => Ok(Decimal::NAN),
        "%" => Ok(Decimal::NAN),
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

fn parse_character(origin: Origin, pair: PestPair) -> Result<Character, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Character);
    let pair = pair.into_inner().next().unwrap();
    parse_unicode_scalar_value(origin, pair).map(Character::from)
}

fn parse_quote(parser: &mut Parser, origin: Origin, pair: PestPair) -> Result<Quote, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Quote);
    let mut words = Vec::new();
    pair.into_inner()
        .try_for_each(|pair| parse_expressions(parser, origin, pair, &mut words))?;

    Ok(words.into_iter().collect())
}

fn parse_string(origin: Origin, pair: PestPair) -> Result<String, ParseError> {
    assert_eq!(pair.as_rule(), Rule::String);
    pair.into_inner()
        .map(|p| parse_unicode_scalar_value(origin, p))
        .collect()
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

fn parse_symbol(origin: Origin, pair: PestPair) -> Result<Symbol, ParseError> {
    assert_eq!(pair.as_rule(), Rule::Symbol);

    let pair = pair.into_inner().next().unwrap();

    match pair.as_rule() {
        Rule::Component => parse_component(origin, pair).map(|c| Symbol::intern(c.as_str())),
        Rule::String => {
            parse_string(origin, pair).map(|s| Symbol::intern(&s.iter().collect::<StdString>()))
        }
        rule => unreachable!("unexpected rule: `{rule:?}`"),
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
    use crate::component::{Component, OwnedComponent};
    use crate::decimal::Decimal;
    use crate::identifier::{Identifier, OwnedIdentifier};
    use crate::integer::Integer;
    use crate::quote::Quote;
    use crate::string::String;
    use crate::word::Word;

    #[test]
    fn parse_word() {
        assert!(Component::try_from_literal(" ans").is_none());
        assert!(Component::try_from_literal("ans ").is_none());
        assert_eq!(
            Component::try_from_literal("ans").unwrap(),
            "ans".parse::<OwnedComponent>().unwrap().borrow()
        );
    }

    #[test]
    fn parse_identifier() {
        assert!(Identifier::try_from_literal(" math/abs").is_none());
        assert!(Identifier::try_from_literal("math/abs ").is_none());
        assert!(Identifier::try_from_literal("math/").is_none());
        assert!(Identifier::try_from_literal("/abs").is_none());
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
        assert!(" [⊥ ⊤ 42 3.14 \"world\" []]".parse::<Quote>().is_err());
        assert!("[⊥ ⊤ 42 3.14 \"world\" []] ".parse::<Quote>().is_err());

        let sut = "[⊥ ⊤ 42 3.14 \"world\" []]".parse::<Quote>().unwrap();

        assert!(matches!(sut[0], Word::Boolean(Boolean(false))));
        assert!(matches!(sut[1], Word::Boolean(Boolean(true))));
        assert!(matches!(sut[2], Word::Integer(Integer(42))));
        assert!(matches!(sut[3], Word::Decimal(Decimal(3.14))));
        assert!(
            matches!(&sut[4], Word::Object(s) if s.downcast_ref::<crate::string::String>().unwrap().iter().copied().eq("world".chars()))
        );
        assert!(
            matches!(&sut[5], Word::Object(q) if q.downcast_ref::<Quote>().unwrap().is_empty())
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
}
