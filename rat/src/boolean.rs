/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

use crate::codegen;
use crate::error::RuntimeError;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;
use crate::expression::Expression;

#[derive(Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Boolean(pub bool);

impl From<bool> for Boolean {
    #[inline]
    fn from(value: bool) -> Self {
        Self(value)
    }
}

impl From<Boolean> for bool {
    #[inline]
    fn from(Boolean(value): Boolean) -> Self {
        value
    }
}

impl Evaluate<Boolean> for &mut Evaluator {
    type Output = Result<(), RuntimeError>;

    fn evaluate(self, value: Boolean) -> Self::Output {
        self.stack.push(Expression::Boolean(value));
        Ok(())
    }
}

codegen::unary_operator!(Boolean, Not::not);

codegen::binary_operator!(Boolean, BitAnd::bitand, BitOr::bitor, BitXor::bitxor);

codegen::binary_assign_operator!(
    Boolean,
    BitAndAssign::bitand_assign,
    BitOrAssign::bitor_assign,
    BitXorAssign::bitxor_assign
);

impl Display for Boolean {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0 {
            false => write!(f, "⊥"),
            true => write!(f, "⊤"),
        }
    }
}

impl Debug for Boolean {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}
