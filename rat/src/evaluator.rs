/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;

use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::expression::Expression;
use crate::globals::Globals;

#[derive(Default)]
pub struct Evaluator {
    pub stack: Vec<Expression>,
    pub globals: Arc<Globals>,
}

impl Evaluator {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn with_globals(globals: Arc<Globals>) -> Self {
        Self {
            stack: Vec::new(),
            globals,
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
