/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::{Debug, Display};
use std::hash::{BuildHasher, DefaultHasher, Hash, Hasher, RandomState};
use std::sync::{Arc, OnceLock};

use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;
use crate::expression::Expression;

#[derive(Clone, PartialEq, Eq)]
pub struct Record {
    entries: Option<Arc<HashMap<Expression, Expression>>>,
}

impl FromIterator<(Expression, Expression)> for Record {
    fn from_iter<T: IntoIterator<Item = (Expression, Expression)>>(entries: T) -> Self {
        let mut entries = entries.into_iter().peekable();
        Self {
            entries: entries
                .peek()
                .is_some()
                .then(|| Arc::new(entries.collect())),
        }
    }
}

impl Default for Record {
    fn default() -> Self {
        Self::new()
    }
}

impl Record {
    pub const fn new() -> Self {
        Self { entries: None }
    }

    pub fn insert(&mut self, key: Expression, value: Expression) -> Option<Expression> {
        Arc::make_mut(self.entries.get_or_insert_with(Default::default)).insert(key, value)
    }

    pub fn contains_key<Q>(&self, key: &Q) -> bool
    where
        Expression: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        self.entries
            .as_ref()
            .map(|e| e.contains_key(key))
            .unwrap_or(false)
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&Expression>
    where
        Expression: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        self.entries.as_ref().and_then(|e| e.get(key))
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<Expression>
    where
        Expression: Borrow<Q>,
        Q: ?Sized + Hash + Eq,
    {
        self.entries
            .as_mut()
            .map(Arc::make_mut)
            .and_then(|e| e.remove(key))
    }

    pub fn len(&self) -> usize {
        self.entries.as_deref().map(HashMap::len).unwrap_or(0)
    }

    pub fn is_empty(&self) -> bool {
        self.entries
            .as_deref()
            .map(HashMap::is_empty)
            .unwrap_or(true)
    }

    pub fn keys(&self) -> Keys {
        Keys::from_delegate(
            self.entries
                .as_deref()
                .unwrap_or_else(empty_hash_map)
                .keys(),
        )
    }

    pub fn values(&self) -> Values {
        Values::from_delegate(
            self.entries
                .as_deref()
                .unwrap_or_else(empty_hash_map)
                .values(),
        )
    }

    pub fn iter(&self) -> Iter {
        Iter::from_delegate(
            self.entries
                .as_deref()
                .unwrap_or_else(empty_hash_map)
                .iter(),
        )
    }

    pub fn into_keys(self) -> IntoKeys {
        IntoKeys::from_delegate(
            self.entries
                .map(|arc| Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone()))
                .unwrap_or_default()
                .into_keys(),
        )
    }

    pub fn into_values(self) -> IntoValues {
        IntoValues::from_delegate(
            self.entries
                .map(|arc| Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone()))
                .unwrap_or_default()
                .into_values(),
        )
    }
}

impl Extend<(Expression, Expression)> for Record {
    fn extend<T: IntoIterator<Item = (Expression, Expression)>>(&mut self, iter: T) {
        Arc::make_mut(self.entries.get_or_insert_with(Default::default)).extend(iter);
    }
}

impl Hash for Record {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let hasher_builder = global_hasher_builder();
        let hash = self
            .entries
            .iter()
            .flat_map(|e| e.iter())
            .map(|pair| hasher_builder.hash_one(pair))
            .fold(18446744073709551557_u64, |l, r| l ^ r);
        state.write_u64(hash);
    }
}

impl Evaluate<Record> for &mut Evaluator {
    type Output = Result<(), Effect>;

    fn evaluate(self, value: Record) -> Self::Output {
        self.stack.push(Expression::Record(value));
        Ok(())
    }
}

impl Display for Record {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        let mut items = self.iter();
        items.next().map(|(k, v)| write!(f, "{k} = {v}"));
        items.try_for_each(|(k, v)| write!(f, ", {k} = {v}"))?;

        write!(f, "}}")
    }
}

impl Debug for Record {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;

        let mut items = self.iter();
        items.next().map(|(k, v)| write!(f, "{k:?} = {v:?}"));
        items.try_for_each(|(k, v)| write!(f, ", {k:?} = {v:?}"))?;

        write!(f, "}}")
    }
}

fn global_hasher_builder<'a>() -> &'a impl BuildHasher<Hasher = DefaultHasher> {
    static INSTANCE: OnceLock<RandomState> = OnceLock::new();
    INSTANCE.get_or_init(Default::default)
}

fn empty_hash_map<'a>() -> &'a HashMap<Expression, Expression> {
    static INSTANCE: OnceLock<HashMap<Expression, Expression>> = OnceLock::new();
    INSTANCE.get_or_init(Default::default)
}

pub struct Keys<'a> {
    delegate: std::collections::hash_map::Keys<'a, Expression, Expression>,
}

impl<'a> Keys<'a> {
    fn from_delegate(
        delegate: std::collections::hash_map::Keys<'a, Expression, Expression>,
    ) -> Self {
        Self { delegate }
    }
}

impl<'a> Iterator for Keys<'a> {
    type Item = <std::collections::hash_map::Keys<'a, Expression, Expression> as Iterator>::Item;

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

impl<'a> std::iter::FusedIterator for Keys<'a> {}

impl<'a> ExactSizeIterator for Keys<'a> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

pub struct Values<'a> {
    delegate: std::collections::hash_map::Values<'a, Expression, Expression>,
}

impl<'a> Values<'a> {
    fn from_delegate(
        delegate: std::collections::hash_map::Values<'a, Expression, Expression>,
    ) -> Self {
        Self { delegate }
    }
}

impl<'a> Iterator for Values<'a> {
    type Item = <std::collections::hash_map::Values<'a, Expression, Expression> as Iterator>::Item;
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

impl<'a> std::iter::FusedIterator for Values<'a> {}

impl<'a> ExactSizeIterator for Values<'a> {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

pub struct Iter<'a> {
    delegate: std::collections::hash_map::Iter<'a, Expression, Expression>,
}

impl<'a> Iter<'a> {
    fn from_delegate(
        delegate: std::collections::hash_map::Iter<'a, Expression, Expression>,
    ) -> Self {
        Self { delegate }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = <std::collections::hash_map::Iter<'a, Expression, Expression> as Iterator>::Item;

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

pub struct IntoKeys {
    delegate: std::collections::hash_map::IntoKeys<Expression, Expression>,
}

impl IntoKeys {
    fn from_delegate(
        delegate: std::collections::hash_map::IntoKeys<Expression, Expression>,
    ) -> Self {
        Self { delegate }
    }
}

impl Iterator for IntoKeys {
    type Item = <std::collections::hash_map::IntoKeys<Expression, Expression> as Iterator>::Item;

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

impl std::iter::FusedIterator for IntoKeys {}

impl ExactSizeIterator for IntoKeys {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

pub struct IntoValues {
    delegate: std::collections::hash_map::IntoValues<Expression, Expression>,
}

impl IntoValues {
    fn from_delegate(
        delegate: std::collections::hash_map::IntoValues<Expression, Expression>,
    ) -> Self {
        Self { delegate }
    }
}

impl Iterator for IntoValues {
    type Item = <std::collections::hash_map::IntoValues<Expression, Expression> as Iterator>::Item;

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

impl std::iter::FusedIterator for IntoValues {}

impl ExactSizeIterator for IntoValues {
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

pub struct IntoIter {
    delegate: std::collections::hash_map::IntoIter<Expression, Expression>,
}

impl IntoIter {
    fn from_delegate(
        delegate: std::collections::hash_map::IntoIter<Expression, Expression>,
    ) -> Self {
        Self { delegate }
    }
}

impl Iterator for IntoIter {
    type Item = <std::collections::hash_map::IntoIter<Expression, Expression> as Iterator>::Item;

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

impl IntoIterator for Record {
    type Item = (Expression, Expression);
    type IntoIter = IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::from_delegate(
            self.entries
                .map(|arc| Arc::try_unwrap(arc).unwrap_or_else(|arc| (*arc).clone()))
                .unwrap_or_default()
                .into_iter(),
        )
    }
}
