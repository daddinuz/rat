/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not};

use crate::codegen;

#[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
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

impl Display for Boolean {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(value) = self;
        match value {
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

codegen::unary_operator!(Boolean, Not::not);

codegen::binary_operator!(Boolean, BitAnd::bitand, BitOr::bitor, BitXor::bitxor);

codegen::binary_assign_operator!(
    Boolean,
    BitAndAssign::bitand_assign,
    BitOrAssign::bitor_assign,
    BitXorAssign::bitxor_assign
);
