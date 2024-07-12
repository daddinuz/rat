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

impl Evaluate<&mut Evaluator> for Expression {
    type Output = Result<(), Effect>;

    fn evaluate(self, evaluator: &mut Evaluator) -> Self::Output {
        match self {
            Expression::Boolean(e) => e.evaluate(evaluator),
            Expression::Decimal(e) => e.evaluate(evaluator),
            Expression::Integer(e) => e.evaluate(evaluator),
            Expression::Process(e) => e.evaluate(evaluator),
            Expression::Quote(e) => e.evaluate(evaluator),
            Expression::String(e) => e.evaluate(evaluator),
            Expression::Symbol(e) => e.evaluate(evaluator),
            Expression::Verb(e) => e.evaluate(evaluator),
        }
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Boolean(e) => Display::fmt(e, f),
            Expression::Decimal(e) => Display::fmt(e, f),
            Expression::Integer(e) => Display::fmt(e, f),
            Expression::Process(e) => Display::fmt(e, f),
            Expression::Quote(e) => Display::fmt(e, f),
            Expression::String(e) => Display::fmt(e, f),
            Expression::Symbol(e) => Display::fmt(e, f),
            Expression::Verb(e) => Display::fmt(e, f),
        }
    }
}

impl Debug for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Expression::Boolean(e) => Debug::fmt(e, f),
            Expression::Decimal(e) => Debug::fmt(e, f),
            Expression::Integer(e) => Debug::fmt(e, f),
            Expression::Process(e) => Debug::fmt(e, f),
            Expression::Quote(e) => Debug::fmt(e, f),
            Expression::String(e) => Debug::fmt(e, f),
            Expression::Symbol(e) => Debug::fmt(e, f),
            Expression::Verb(e) => Debug::fmt(e, f),
        }
    }
}
