/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use ustr::Ustr;

use crate::error::RuntimeError;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;
use crate::expression::Expression;

use std::fmt::{Debug, Display};

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(Ustr);

impl FromIterator<char> for Symbol {
    fn from_iter<I: IntoIterator<Item = char>>(chars: I) -> Self {
        Self(Ustr::from(chars.into_iter().collect::<String>().as_str()))
    }
}

impl Symbol {
    pub fn new(s: &str) -> Self {
        Symbol(Ustr::from(s))
    }

    pub fn divide_by_zero() -> Symbol {
        Symbol::new("DivideByZero")
    }

    pub fn stack_underflow() -> Symbol {
        Symbol::new("StackUnderflow")
    }

    pub fn out_of_range() -> Symbol {
        Symbol::new("OutOfRange")
    }

    pub fn type_error() -> Symbol {
        Symbol::new("TypeError")
    }

    pub fn io_error() -> Symbol {
        Symbol::new("IOError")
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Evaluate<Symbol> for &mut Evaluator {
    type Output = Result<(), RuntimeError>;

    fn evaluate(self, value: Symbol) -> Self::Output {
        self.stack.push(Expression::Symbol(value));
        Ok(())
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(s) = self;
        write!(f, "{}", s)
    }
}

impl Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(s) = self;
        write!(f, "$\"{}\"", s)
    }
}

#[cfg(test)]
mod test {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{BuildHasher, BuildHasherDefault};

    use super::*;

    #[test]
    fn identity() {
        let sut1 = Symbol::new("hello");
        let sut2 = Symbol::new("hello");
        let sut3 = Symbol::new("world");

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
}
