/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};
use std::ops::{Index, IndexMut};
use std::slice::SliceIndex;

#[derive(Clone, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct String(Vec<char>);

impl FromIterator<char> for String {
    #[inline]
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

impl<const N: usize> From<[char; N]> for String {
    #[inline]
    fn from(value: [char; N]) -> Self {
        Self(value.into())
    }
}

impl Extend<char> for String {
    #[inline]
    fn extend<T: IntoIterator<Item = char>>(&mut self, iter: T) {
        let Self(inner) = self;
        inner.extend(iter);
    }
}

impl String {
    #[inline]
    pub const fn new() -> Self {
        Self(Vec::new())
    }

    #[inline]
    pub fn extend_from_slice(&mut self, slice: &[char]) {
        let Self(inner) = self;
        inner.extend_from_slice(slice);
    }

    #[inline]
    pub fn push(&mut self, word: char) {
        let Self(inner) = self;
        inner.push(word);
    }

    #[inline]
    pub fn pop(&mut self) -> Option<char> {
        let Self(inner) = self;
        inner.pop()
    }

    #[inline]
    pub fn first(&self) -> Option<&char> {
        let Self(inner) = self;
        inner.first()
    }

    #[inline]
    pub fn first_mut(&mut self) -> Option<&mut char> {
        let Self(inner) = self;
        inner.first_mut()
    }

    #[inline]
    pub fn last(&self) -> Option<&char> {
        let Self(inner) = self;
        inner.last()
    }

    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut char> {
        let Self(inner) = self;
        inner.last_mut()
    }

    #[inline]
    pub fn get<I>(&self, index: I) -> Option<&I::Output>
    where
        I: SliceIndex<[char]>,
    {
        let Self(inner) = self;
        inner.get(index)
    }

    #[inline]
    pub fn get_mut<I>(&mut self, index: I) -> Option<&mut I::Output>
    where
        I: SliceIndex<[char]>,
    {
        let Self(inner) = self;
        inner.get_mut(index)
    }

    #[inline]
    pub fn truncate(&mut self, len: usize) {
        let Self(inner) = self;
        inner.truncate(len);
    }

    #[inline]
    pub fn clear(&mut self) {
        let Self(inner) = self;
        inner.clear();
    }

    #[inline]
    pub const fn is_empty(&self) -> bool {
        let Self(inner) = self;
        inner.is_empty()
    }

    #[inline]
    pub const fn len(&self) -> usize {
        let Self(inner) = self;
        inner.len()
    }

    #[inline]
    pub const fn capacity(&self) -> usize {
        let Self(inner) = self;
        inner.capacity()
    }

    #[inline]
    pub const fn as_slice(&self) -> &[char] {
        let Self(inner) = self;
        inner.as_slice()
    }

    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [char] {
        let Self(inner) = self;
        inner.as_mut_slice()
    }

    #[inline]
    pub fn iter(&self) -> Iter<'_> {
        let Self(inner) = self;
        Iter::from_delegate(inner.iter())
    }

    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        let Self(inner) = self;
        IterMut::from_delegate(inner.iter_mut())
    }
}

impl<I: SliceIndex<[char]>> Index<I> for String {
    type Output = I::Output;

    #[inline]
    fn index(&self, index: I) -> &Self::Output {
        let Self(inner) = self;
        &inner[index]
    }
}

impl<I: SliceIndex<[char]>> IndexMut<I> for String {
    #[inline]
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        let Self(inner) = self;
        &mut inner[index]
    }
}

impl Debug for String {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "\"")?;

        self.iter()
            .try_for_each(|c| write!(f, "{}", c.escape_debug()))?;

        write!(f, "\"")
    }
}

impl Display for String {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.iter().try_for_each(|c| write!(f, "{c}"))
    }
}

pub struct Iter<'a> {
    delegate: std::slice::Iter<'a, char>,
}

impl<'a> Iter<'a> {
    #[inline]
    const fn from_delegate(delegate: std::slice::Iter<'a, char>) -> Self {
        Self { delegate }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = <std::slice::Iter<'a, char> as Iterator>::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.delegate.size_hint()
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.delegate.count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.delegate.next_back()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n)
    }
}

impl std::iter::FusedIterator for Iter<'_> {}

impl ExactSizeIterator for Iter<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl DoubleEndedIterator for Iter<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n)
    }
}

pub struct IterMut<'a> {
    delegate: std::slice::IterMut<'a, char>,
}

impl<'a> IterMut<'a> {
    #[inline]
    const fn from_delegate(delegate: std::slice::IterMut<'a, char>) -> Self {
        Self { delegate }
    }
}

impl<'a> Iterator for IterMut<'a> {
    type Item = <std::slice::IterMut<'a, char> as Iterator>::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.delegate.size_hint()
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.delegate.count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.delegate.next_back()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n)
    }
}

impl std::iter::FusedIterator for IterMut<'_> {}

impl ExactSizeIterator for IterMut<'_> {
    #[inline]
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl DoubleEndedIterator for IterMut<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n)
    }
}

pub struct IntoIter {
    delegate: std::vec::IntoIter<char>,
}

impl IntoIter {
    #[inline]
    fn from_delegate(delegate: std::vec::IntoIter<char>) -> Self {
        Self { delegate }
    }
}

impl Iterator for IntoIter {
    type Item = <std::vec::IntoIter<char> as Iterator>::Item;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.delegate.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.delegate.size_hint()
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        self.delegate.count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.delegate.next_back()
    }

    #[inline]
    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth(n)
    }
}

impl std::iter::FusedIterator for IntoIter {}

impl ExactSizeIterator for IntoIter {
    #[inline]
    fn len(&self) -> usize {
        self.delegate.len()
    }
}

impl DoubleEndedIterator for IntoIter {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        self.delegate.next_back()
    }

    #[inline]
    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        self.delegate.nth_back(n)
    }
}

impl IntoIterator for String {
    type Item = char;
    type IntoIter = IntoIter;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let Self(inner) = self;
        IntoIter::from_delegate(inner.into_iter())
    }
}

impl<'a> IntoIterator for &'a String {
    type Item = &'a char;
    type IntoIter = std::slice::Iter<'a, char>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let String(inner) = self;
        inner.iter()
    }
}

impl<'a> IntoIterator for &'a mut String {
    type Item = &'a mut char;
    type IntoIter = std::slice::IterMut<'a, char>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        let String(inner) = self;
        inner.iter_mut()
    }
}
