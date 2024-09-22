/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use crate::error::RuntimeError;
use crate::evaluate::Evaluate;
use crate::expression::Expression;

#[derive(Default)]
pub struct Evaluator {
    pub stack: Vec<Expression>,
}

impl Evaluator {
    pub fn new() -> Self {
        Default::default()
    }
}

impl<I> Evaluate<I> for &mut Evaluator
where
    I: Iterator<Item = Expression>,
{
    type Output = Result<(), RuntimeError>;

    fn evaluate(self, mut expressions: I) -> Self::Output {
        expressions.try_for_each(|e| self.evaluate(e))
    }
}
