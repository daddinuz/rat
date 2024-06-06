/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::error::Error;
use std::fmt::{Debug, Display};

use ustr::Ustr;

use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;
use crate::expression::Expression;

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Signal(Ustr);

impl Signal {
    // FIXME
    /**
     * SAFETY
     * This rat does not validate input string so it can be called with invalid signal literals.
     */
    pub(crate) unsafe fn new(literal: &str) -> Self {
        Self(Ustr::from(literal))
    }

    pub fn try_trom_literal(literal: &str) -> Result<Self, InvalidSignalLiteral> {
        if literal.len() > 1
            && literal
                .strip_prefix('$')
                .map(|s| s.bytes().all(|byte| byte.is_ascii_alphabetic()))
                .unwrap_or(false)
        {
            return Ok(unsafe { Self::new(&literal[1..]) });
        }

        Err(InvalidSignalLiteral)
    }
}

pub fn divide_by_zero() -> Signal {
    unsafe { Signal::new("DivideByZero") }
}

pub fn stack_underflow() -> Signal {
    unsafe { Signal::new("StackUnderflow") }
}

pub fn out_of_range() -> Signal {
    unsafe { Signal::new("OutOfRange") }
}

pub fn type_error() -> Signal {
    unsafe { Signal::new("TypeError") }
}

pub fn io_error() -> Signal {
    unsafe { Signal::new("IOError") }
}

impl Evaluate<&mut Evaluator> for Signal {
    type Output = Result<(), Effect>;

    fn evaluate(self, evaluator: &mut Evaluator) -> Self::Output {
        evaluator.stack.push(Expression::Signal(self));
        Ok(())
    }
}

impl Display for Signal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(s) = self;
        write!(f, "${s}")
    }
}

impl Debug for Signal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InvalidSignalLiteral;

impl Display for InvalidSignalLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Error for InvalidSignalLiteral {}

#[cfg(test)]
mod test {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{BuildHasher, BuildHasherDefault};

    use super::*;

    #[test]
    fn identity() {
        let sut1 = stack_underflow();
        let sut2 = stack_underflow();
        let sut3 = io_error();

        assert_eq!(sut1, sut2);
        assert_eq!(sut1, sut2);

        assert_ne!(sut1, sut3);
        assert_ne!(sut1, sut3);

        assert_ne!(sut2, sut3);
        assert_ne!(sut2, sut3);

        let hash_builder = BuildHasherDefault::<DefaultHasher>::default();
        let h1 = hash_builder.hash_one(sut1);
        let h2 = hash_builder.hash_one(sut2);
        assert_eq!(h1, h2);
    }

    #[test]
    fn try_from_literal() {
        assert_eq!(io_error(), Signal::try_trom_literal("$IOError").unwrap());
        assert!(Signal::try_trom_literal("$").is_err());
        assert!(Signal::try_trom_literal("$x!").is_err());
        assert!(Signal::try_trom_literal("$x42").is_err());
        assert!(Signal::try_trom_literal("IoError").is_err());
    }
}
