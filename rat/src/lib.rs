/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

#[macro_use]
extern crate pest_derive;

pub(crate) mod codegen;

pub mod boolean;
pub mod channel;
pub mod decimal;
pub mod integer;
pub mod quote;
pub mod signal;
pub mod string;
pub mod symbol;
pub mod verb;

pub mod expression;

pub mod builtin;
pub mod effect;
pub mod evaluate;
pub mod evaluator;
pub mod parser;
pub mod source;
pub mod vocabulary;
pub mod word;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[cfg(test)]
mod test {
    use crate::evaluate::Evaluate;
    use crate::evaluator::Evaluator;
    use crate::expression::Expression;
    use crate::integer::Integer;
    use crate::verb::Verb;
    use crate::{builtin, signal};

    #[test]
    fn it_works1() {
        let mut evaluator = Evaluator::default();
        evaluator
            .evaluate([
                Expression::Integer(Integer(64)),
                Expression::Integer(Integer(22)),
                Expression::Quote([Expression::Verb(Verb(builtin::sub))].into_iter().collect()),
                Expression::Verb(Verb(builtin::unquote)),
            ])
            .unwrap();

        assert!(matches!(
            evaluator.stack.as_slice(),
            &[Expression::Integer(Integer(42))]
        ));
    }

    #[test]
    fn it_works2() {
        let mut evaluator = Evaluator::default();
        evaluator
            .evaluate([
                Expression::Integer(Integer(1)),
                Expression::Quote(
                    [
                        Expression::Integer(Integer(2)),
                        Expression::Integer(Integer(1)),
                        Expression::Verb(Verb(builtin::sub)),
                        Expression::Verb(Verb(builtin::r#yield)),
                        Expression::Verb(Verb(builtin::sub)),
                    ]
                    .into_iter()
                    .collect(),
                ),
                Expression::Verb(Verb(builtin::unquote)),
                Expression::Verb(Verb(builtin::unquote)),
            ])
            .unwrap();

        assert!(matches!(
            evaluator.stack.as_slice(),
            &[Expression::Integer(Integer(0))]
        ));
    }

    #[test]
    fn it_works3() {
        let mut evaluator = Evaluator::default();
        evaluator
            .evaluate([
                Expression::Quote(
                    [
                        Expression::Integer(Integer(1)),
                        Expression::Verb(Verb(builtin::sub)),
                    ]
                    .into_iter()
                    .collect(),
                ),
                Expression::Quote([Expression::Integer(Integer(42))].into_iter().collect()),
                Expression::Signal(signal::stack_underflow()),
                Expression::Verb(Verb(builtin::catch)),
            ])
            .unwrap();

        assert!(matches!(
            evaluator.stack.as_slice(),
            &[Expression::Integer(Integer(42))]
        ));
    }

    #[test]
    fn it_works4() {
        let mut evaluator = Evaluator::default();
        evaluator
            .evaluate([
                Expression::Quote(
                    [
                        Expression::Integer(Integer(8)),
                        Expression::Integer(Integer(12)),
                        Expression::Verb(Verb(builtin::add)),
                        Expression::Verb(Verb(builtin::produce)),
                    ]
                    .into_iter()
                    .collect(),
                ),
                Expression::Verb(Verb(builtin::spawn)),
                Expression::Quote(
                    [
                        Expression::Integer(Integer(10)),
                        Expression::Integer(Integer(12)),
                        Expression::Verb(Verb(builtin::add)),
                        Expression::Verb(Verb(builtin::produce)),
                    ]
                    .into_iter()
                    .collect(),
                ),
                Expression::Verb(Verb(builtin::spawn)),
                Expression::Verb(Verb(builtin::receive)),
                Expression::Verb(Verb(builtin::swap)),
                Expression::Verb(Verb(builtin::pop)),
                Expression::Verb(Verb(builtin::swap)),
                Expression::Verb(Verb(builtin::receive)),
                Expression::Verb(Verb(builtin::swap)),
                Expression::Verb(Verb(builtin::pop)),
                Expression::Verb(Verb(builtin::add)),
            ])
            .unwrap();

        assert!(matches!(
            evaluator.stack.as_slice(),
            &[Expression::Integer(Integer(42))]
        ));
    }
}
