/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};

use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;

use crate::boolean::Boolean;
use crate::decimal::Decimal;
use crate::integer::Integer;
use crate::process::Process;
use crate::quote::Quote;
use crate::string::String;
use crate::symbol::Symbol;
use crate::verb::Verb;

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Expression {
    Boolean(Boolean),
    Decimal(Decimal),
    Integer(Integer),
    Process(Process),
    Quote(Quote),
    String(String),
    Symbol(Symbol),
    Verb(Verb),
}

const _: [(); 16] = [(); std::mem::size_of::<Expression>()];
const _: [(); 1] = [(); std::mem::size_of::<Result<(), Effect>>()];

impl From<Boolean> for Expression {
    #[inline]
    fn from(value: Boolean) -> Self {
        Self::Boolean(value)
    }
}

impl From<Decimal> for Expression {
    #[inline]
    fn from(value: Decimal) -> Self {
        Self::Decimal(value)
    }
}

impl From<Integer> for Expression {
    #[inline]
    fn from(value: Integer) -> Self {
        Self::Integer(value)
    }
}

impl From<Process> for Expression {
    #[inline]
    fn from(value: Process) -> Self {
        Self::Process(value)
    }
}

impl From<Quote> for Expression {
    #[inline]
    fn from(value: Quote) -> Self {
        Self::Quote(value)
    }
}

impl From<String> for Expression {
    #[inline]
    fn from(value: String) -> Self {
        Self::String(value)
    }
}

impl From<Symbol> for Expression {
    #[inline]
    fn from(value: Symbol) -> Self {
        Self::Symbol(value)
    }
}

impl From<Verb> for Expression {
    #[inline]
    fn from(value: Verb) -> Self {
        Self::Verb(value)
    }
}

impl Evaluate<Expression> for &mut Evaluator {
    type Output = Result<(), Effect>;

    fn evaluate(self, expression: Expression) -> Self::Output {
        match expression {
            Expression::Boolean(v) => self.evaluate(v),
            Expression::Decimal(v) => self.evaluate(v),
            Expression::Integer(v) => self.evaluate(v),
            Expression::Process(v) => self.evaluate(v),
            Expression::Quote(v) => self.evaluate(v),
            Expression::String(v) => self.evaluate(v),
            Expression::Symbol(v) => self.evaluate(v),
            Expression::Verb(v) => self.evaluate(v),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Boolean(v) => Display::fmt(v, f),
            Expression::Decimal(v) => Display::fmt(v, f),
            Expression::Integer(v) => Display::fmt(v, f),
            Expression::Process(v) => Display::fmt(v, f),
            Expression::Quote(v) => Display::fmt(v, f),
            Expression::String(v) => Display::fmt(v, f),
            Expression::Symbol(v) => Display::fmt(v, f),
            Expression::Verb(v) => Display::fmt(v, f),
        }
    }
}

impl Debug for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Boolean(v) => Debug::fmt(v, f),
            Expression::Decimal(v) => Debug::fmt(v, f),
            Expression::Integer(v) => Debug::fmt(v, f),
            Expression::Process(v) => Debug::fmt(v, f),
            Expression::Quote(v) => Debug::fmt(v, f),
            Expression::String(v) => Debug::fmt(v, f),
            Expression::Symbol(v) => Debug::fmt(v, f),
            Expression::Verb(v) => Debug::fmt(v, f),
        }
    }
}
