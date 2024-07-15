/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::Arc;
use std::thread::{self};

use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;
use crate::expression::Expression;
use crate::globals::Globals;
use crate::quote::Quote;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Process {
    quote: Quote,
}

impl Process {
    pub fn spawn(globals: Arc<Globals>, quote: Quote) -> Self {
        {
            let quote = quote.clone();
            thread::spawn(move || {
                let mut evaluator = Evaluator::with_globals(globals);
                evaluator.evaluate(quote)
            });
        }

        Self { quote }
    }
}

impl Evaluate<Process> for &mut Evaluator {
    type Output = Result<(), Effect>;

    fn evaluate(self, value: Process) -> Self::Output {
        self.stack.push(Expression::Process(value));
        Ok(())
    }
}

impl Display for Process {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Debug for Process {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "${:?}", self.quote)
    }
}
