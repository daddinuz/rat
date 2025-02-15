/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#[macro_use]
extern crate pest_derive;

pub(crate) mod codegen;

pub mod boolean;
pub mod decimal;
pub mod integer;
pub mod quote;
pub mod string;
pub mod symbol;
pub mod verb;

pub mod expression;

pub mod builtin;
pub mod dictionary;
pub mod error;
pub mod evaluate;
pub mod evaluator;
pub mod identifier;
pub mod parser;
pub mod word;

use std::env;
use std::path::Path;
use std::sync::OnceLock;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[allow(deprecated)]
pub fn home_dir() -> &'static Path {
    static HOME_DIR: OnceLock<Box<Path>> = OnceLock::new();

    HOME_DIR
        .get_or_init(|| {
            dirs::home_dir()
                .or_else(env::home_dir)
                .unwrap_or_default()
                .join(".rat")
                .into()
        })
        .as_ref()
}

#[cfg(test)]
mod test {
    use crate::boolean::Boolean;
    use crate::builtin;
    use crate::evaluate::Evaluate;
    use crate::evaluator::Evaluator;
    use crate::expression::Expression;
    use crate::integer::Integer;
    use crate::symbol::Symbol;
    use crate::verb::Verb;

    use std::path::Path;
    use std::process::Command;

    #[test]
    fn it_works1() {
        let mut evaluator = Evaluator::default();
        evaluator
            .evaluate(
                [
                    Expression::Integer(Integer(64)),
                    Expression::Integer(Integer(22)),
                    Expression::Quote([Expression::Verb(Verb(builtin::sub))].into_iter().collect()),
                    Expression::Verb(Verb(builtin::unquote)),
                ]
                .into_iter(),
            )
            .unwrap();

        assert_eq!(
            evaluator.stack.as_slice(),
            &[Expression::Integer(Integer(42))]
        );
    }

    #[test]
    fn it_works2() {
        let mut evaluator = Evaluator::default();
        evaluator
            .evaluate(
                [
                    Expression::Quote(
                        [
                            Expression::Integer(Integer(1)),
                            Expression::Verb(Verb(builtin::sub)),
                        ]
                        .into_iter()
                        .collect(),
                    ),
                    Expression::Quote([Expression::Integer(Integer(42))].into_iter().collect()),
                    Expression::Symbol(Symbol::stack_underflow()),
                    Expression::Verb(Verb(builtin::r#try)),
                ]
                .into_iter(),
            )
            .unwrap();

        assert_eq!(
            evaluator.stack.as_slice(),
            &[Expression::Integer(Integer(42))]
        );
    }

    #[test]
    fn it_works3() {
        let mut evaluator = Evaluator::default();
        evaluator
            .evaluate(
                [
                    // if
                    Expression::Boolean(Boolean(true)),
                    Expression::Quote([Expression::Integer(42.into())].into_iter().collect()),
                    Expression::Verb(Verb(builtin::r#if)),
                    Expression::Boolean(Boolean(false)),
                    Expression::Quote([Expression::Integer(42.into())].into_iter().collect()),
                    Expression::Verb(Verb(builtin::r#if)),
                    // else
                    Expression::Boolean(Boolean(true)),
                    Expression::Quote([Expression::Integer(42.into())].into_iter().collect()),
                    Expression::Verb(Verb(builtin::r#else)),
                    Expression::Boolean(Boolean(false)),
                    Expression::Quote([Expression::Integer(42.into())].into_iter().collect()),
                    Expression::Verb(Verb(builtin::r#else)),
                    // if-else
                    Expression::Boolean(Boolean(true)),
                    Expression::Quote([Expression::Integer(42.into())].into_iter().collect()),
                    Expression::Quote([Expression::Integer(24.into())].into_iter().collect()),
                    Expression::Verb(Verb(builtin::if_else)),
                    Expression::Boolean(Boolean(false)),
                    Expression::Quote([Expression::Integer(24.into())].into_iter().collect()),
                    Expression::Quote([Expression::Integer(42.into())].into_iter().collect()),
                    Expression::Verb(Verb(builtin::if_else)),
                ]
                .into_iter(),
            )
            .unwrap();

        assert_eq!(
            evaluator.stack.as_slice(),
            &[
                Expression::Integer(Integer(42)),
                Expression::Integer(Integer(42)),
                Expression::Integer(Integer(42)),
                Expression::Integer(Integer(42))
            ]
        );
    }

    #[test]
    fn word_and_grammar_are_aligned() {
        let grammar_path = Path::new(env!("CARGO_WORKSPACE_DIR")).join("rat/src/grammar.pest");
        let word_path = Path::new(env!("CARGO_WORKSPACE_DIR")).join("rat/src/word.rs");
        let output = Command::new("md5sum")
            .arg(&grammar_path)
            .arg(&word_path)
            .output()
            .unwrap();

        assert_eq!(
            &output.stdout,
            format!(
                "c55d29c3dd9298a203dfc945d9c238cc  {}\nab5aa40ceddd0bc08fbf445cd9fe054e  {}\n",
                grammar_path.display(),
                word_path.display()
            )
            .as_bytes()
        );
    }
}
