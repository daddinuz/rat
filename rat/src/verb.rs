/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};

use crate::error::RuntimeError;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Verb(pub fn(&mut Evaluator) -> Result<(), RuntimeError>);

impl Evaluate<Verb> for &mut Evaluator {
    type Output = Result<(), RuntimeError>;

    fn evaluate(self, Verb(verb): Verb) -> Self::Output {
        verb(self)
    }
}

impl Display for Verb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Debug for Verb {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(verb) = self;
        write!(f, "{:p}", *verb)
    }
}
