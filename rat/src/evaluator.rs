/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use crossbeam::channel::{Receiver, Sender};

use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::expression::Expression;

pub struct Evaluator {
    pub stack: Vec<Expression>,
    pub channel: Option<(Sender<Expression>, Receiver<Expression>)>,
}

impl Default for Evaluator {
    fn default() -> Self {
        Self::new()
    }
}

impl Evaluator {
    pub const fn new() -> Self {
        Self {
            stack: Vec::new(),
            channel: None,
        }
    }
}

impl<P> Evaluate<P> for &mut Evaluator
where
    P: IntoIterator<Item = Expression>,
{
    type Output = Result<(), Effect>;

    fn evaluate(self, program: P) -> Self::Output {
        program.into_iter().try_for_each(|e| e.evaluate(self))
    }
}

impl Evaluate<Expression> for &mut Evaluator {
    type Output = Result<(), Effect>;

    fn evaluate(self, expression: Expression) -> Self::Output {
        expression.evaluate(self)
    }
}
