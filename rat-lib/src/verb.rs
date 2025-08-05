/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};

use crate::context::Context;
use crate::symbol::Symbol;

#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct Verb(pub fn(&mut Context) -> Result<(), Symbol>);

impl Verb {
    #[inline]
    pub fn apply(self, context: &mut Context) -> Result<(), Symbol> {
        let Self(verb) = self;
        verb(context)
    }
}

impl Debug for Verb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(verb) = self;
        write!(f, "ƒ⟨{:p}⟩", *verb)
    }
}

impl Display for Verb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}
