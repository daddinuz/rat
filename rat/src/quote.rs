/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};
use std::ops::Deref;
use std::sync::Arc;

use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;
use crate::expression::Expression;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Quote {
    inner: Option<Arc<Vec<Expression>>>,
}

impl FromIterator<Expression> for Quote {
    fn from_iter<I: IntoIterator<Item = Expression>>(expressions: I) -> Self {
        let mut expressions = expressions.into_iter().peekable();

        Self {
            inner: expressions
                .peek()
                .is_some()
                .then(|| Arc::new(expressions.collect())),
        }
    }
}

impl<const N: usize> From<[Expression; N]> for Quote {
    fn from(value: [Expression; N]) -> Self {
        Self::from_iter(value)
    }
}

impl Default for Quote {
    fn default() -> Self {
        Self::new()
    }
}

impl Quote {
    pub const fn new() -> Self {
        Self { inner: None }
    }

    pub fn insert(&mut self, index: usize, expression: Expression) {
        Arc::make_mut(self.inner.get_or_insert_with(Default::default)).insert(index, expression);
    }

    pub fn push(&mut self, expression: Expression) {
        Arc::make_mut(self.inner.get_or_insert_with(Default::default)).push(expression);
    }

    pub fn pop(&mut self) -> Option<Expression> {
        self.inner.as_mut().map(Arc::make_mut).and_then(Vec::pop)
    }

    pub fn remove(&mut self, index: usize) -> Option<Expression> {
        self.inner
            .as_mut()
            .filter(|v| index < v.len())
            .map(Arc::make_mut)
            .map(|v| v.remove(index))
    }

    pub fn split(&mut self, at: usize) -> Quote {
        self.inner
            .as_mut()
            .map(Arc::make_mut)
            .map(|v| Self {
                inner: Some(Arc::new(v.split_off(at))),
            })
            .unwrap()
    }

    pub fn as_slice(&self) -> &[Expression] {
        self.inner.as_deref().map(Deref::deref).unwrap_or(&[])
    }

    pub fn iter(&self) -> Iter {
        Iter::from_delegate(
            self.inner
                .as_deref()
                .map(Deref::deref)
                .unwrap_or(&[])
                .iter(),
        )
    }
}

impl Evaluate<&mut Evaluator> for Quote {
    type Output = Result<(), Effect>;

    fn evaluate(self, evaluator: &mut Evaluator) -> Self::Output {
        evaluator.stack.push(Expression::Quote(self));
        Ok(())
    }
}

impl Deref for Quote {
    type Target = [Expression];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl Display for Quote {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        DisplayAdapter::new(self.as_slice()).display().fmt(f)
    }
}

impl Debug for Quote {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        DisplayAdapter::new(self.as_slice()).debug().fmt(f)
    }
}

impl Extend<Expression> for Quote {
    fn extend<T: IntoIterator<Item = Expression>>(&mut self, iter: T) {
        Arc::make_mut(self.inner.get_or_insert_with(Default::default)).extend(iter);
    }
}

pub struct Iter<'a> {
    delegate: std::slice::Iter<'a, Expression>,
}

impl<'a> Iter<'a> {
    fn from_delegate(delegate: std::slice::Iter<'a, Expression>) -> Self {
        Self { delegate }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = <std::slice::Iter<'a, Expression> as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.delegate.size_hint()
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.delegate.count()
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.delegate.last()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n)
    }
}

impl<'a> std::iter::FusedIterator for Iter<'a> {}

impl<'a> ExactSizeIterator for Iter<'a> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl<'a> DoubleEndedIterator for Iter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back()
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n)
    }
}

pub struct IntoIter {
    delegate: std::vec::IntoIter<Expression>,
}

impl IntoIter {
    fn from_delegate(delegate: std::vec::IntoIter<Expression>) -> Self {
        Self { delegate }
    }
}

impl Iterator for IntoIter {
    type Item = <std::vec::IntoIter<Expression> as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.delegate.size_hint()
    }

    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.delegate.count()
    }

    fn last(self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.delegate.last()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n)
    }
}

impl std::iter::FusedIterator for IntoIter {}

impl ExactSizeIterator for IntoIter {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl DoubleEndedIterator for IntoIter {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back()
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n)
    }
}

impl IntoIterator for Quote {
    type Item = Expression;
    type IntoIter = IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::from_delegate(
            self.inner
                .map(|arc| Arc::try_unwrap(arc).unwrap_or_else(|v| (*v).clone()))
                .unwrap_or_default()
                .into_iter(),
        )
    }
}

pub struct DisplayAdapter<'a> {
    slice: &'a [Expression],
}

impl<'a> DisplayAdapter<'a> {
    pub const fn new(slice: &'a [Expression]) -> Self {
        Self { slice }
    }

    pub fn display(&self) -> impl Display + '_ {
        self
    }

    pub fn debug(&self) -> impl Debug + '_ {
        self
    }
}

impl<'a> Display for DisplayAdapter<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.slice {
            [] => write!(f, "[]"),
            [v] => write!(f, "[{v}]"),
            [v, rest @ ..] => {
                write!(f, "[{v}")?;
                for v in rest {
                    write!(f, " {v}")?;
                }
                write!(f, "]")
            }
        }
    }
}

impl<'a> Debug for DisplayAdapter<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.slice {
            [] => write!(f, "[]"),
            [v] => write!(f, "[{v:?}]"),
            [v, rest @ ..] => {
                write!(f, "[{v:?}")?;
                for v in rest {
                    write!(f, " {v:?}")?;
                }
                write!(f, "]")
            }
        }
    }
}
