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

#[derive(Default, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct String {
    chars: Option<Arc<Vec<char>>>,
}

impl FromIterator<char> for String {
    fn from_iter<I: IntoIterator<Item = char>>(chars: I) -> Self {
        let mut chars = chars.into_iter().peekable();

        Self {
            chars: chars.peek().is_some().then(|| Arc::new(chars.collect())),
        }
    }
}

impl String {
    pub const fn new() -> Self {
        Self { chars: None }
    }

    pub fn from_utf8(s: &str) -> Self {
        s.chars().collect()
    }

    pub fn insert(&mut self, index: usize, c: char) {
        Arc::make_mut(self.chars.get_or_insert_with(Default::default)).insert(index, c);
    }

    pub fn push(&mut self, c: char) {
        Arc::make_mut(self.chars.get_or_insert_with(Default::default)).push(c);
    }

    pub fn pop(&mut self) -> Option<char> {
        self.chars.as_mut().map(Arc::make_mut).and_then(Vec::pop)
    }

    pub fn remove(&mut self, index: usize) -> Option<char> {
        self.chars
            .as_mut()
            .filter(|v| index < v.len())
            .map(Arc::make_mut)
            .map(|v| v.remove(index))
    }

    pub fn iter(&self) -> Iter {
        Iter::from_delegate(
            self.chars
                .as_deref()
                .map(Vec::as_slice)
                .unwrap_or(&[])
                .iter(),
        )
    }
}

impl Evaluate<String> for &mut Evaluator {
    type Output = Result<(), Effect>;

    fn evaluate(self, value: String) -> Self::Output {
        self.stack.push(Expression::String(value));
        Ok(())
    }
}

impl Deref for String {
    type Target = [char];

    fn deref(&self) -> &Self::Target {
        self.chars.as_deref().map(Deref::deref).unwrap_or(&[])
    }
}

impl Display for String {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.iter().try_for_each(|c| write!(f, "{c}"))
    }
}

impl Debug for String {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"")?;

        self.iter()
            .copied()
            .flat_map(char::escape_debug)
            .try_for_each(|c| write!(f, "{c}"))?;

        write!(f, "\"")
    }
}

impl Extend<char> for String {
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        Arc::make_mut(self.chars.get_or_insert_with(Default::default)).extend(iter);
    }
}

pub struct Iter<'a> {
    delegate: std::slice::Iter<'a, char>,
}

impl<'a> Iter<'a> {
    fn from_delegate(delegate: std::slice::Iter<'a, char>) -> Self {
        Self { delegate }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = <std::slice::Iter<'a, char> as Iterator>::Item;

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
    delegate: std::vec::IntoIter<char>,
}

impl IntoIter {
    fn from_delegate(delegate: std::vec::IntoIter<char>) -> Self {
        Self { delegate }
    }
}

impl Iterator for IntoIter {
    type Item = <std::vec::IntoIter<char> as Iterator>::Item;

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

impl IntoIterator for String {
    type Item = char;
    type IntoIter = IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::from_delegate(
            self.chars
                .map(|arc| Arc::try_unwrap(arc).unwrap_or_else(|v| (*v).clone()))
                .unwrap_or_default()
                .into_iter(),
        )
    }
}
