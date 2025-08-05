/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::borrow::Borrow;
use std::fmt::{Debug, Display};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Component(str);

impl ToOwned for Component {
    type Owned = OwnedComponent;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        let Self(inner) = self;
        OwnedComponent(inner.into())
    }
}

impl Component {
    /// Whitespaces are not allowed in `literal`.
    // TODO: this must always be kept in sync with `grammar.pest`
    pub const fn try_from_literal(literal: &str) -> Option<&Self> {
        let bytes = literal.as_bytes();

        if Self::is_valid(bytes, 0, bytes.len()) {
            return unsafe { Some(Self::new(literal)) };
        }

        None
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        let Self(inner) = self;
        inner
    }

    #[inline]
    pub(crate) const unsafe fn new(literal: &str) -> &Self {
        let inner = literal as *const str as *const Self;
        // Safety: `Component` is a `repr(transparent)` wrapper around `str`
        // have a look at: https://stackoverflow.com/a/72106272
        unsafe { &*inner }
    }

    pub(crate) const fn is_valid(bytes: &[u8], start: usize, end: usize) -> bool {
        if start >= end || end > bytes.len() {
            return false;
        }

        let mut i = start;
        let mut state = 0;

        while i < end {
            let c = bytes[i];

            match state {
                0 if c.is_ascii_alphabetic() => {
                    state = 1;
                    i += 1;
                    continue;
                }
                1 if c == b'-' => {
                    state = 0;
                    i += 1;
                    continue;
                }
                1 if c == b'!' => {
                    state = 2;
                    i += 1;
                    continue;
                }
                1 if c == b'?' => {
                    i += 1;
                    break;
                }
                1 if c.is_ascii_alphanumeric() => {
                    i += 1;
                    continue;
                }
                2 if c == b'?' => {
                    i += 1;
                    break;
                }
                _ => break,
            }
        }

        end == i && state != 0
    }
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OwnedComponent(Box<str>);

impl From<&Component> for OwnedComponent {
    #[inline]
    fn from(component: &Component) -> Self {
        component.to_owned()
    }
}

impl Borrow<Component> for OwnedComponent {
    fn borrow(&self) -> &Component {
        unsafe { Component::new(self.as_str()) }
    }
}

impl Display for OwnedComponent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for OwnedComponent {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

impl OwnedComponent {
    #[inline]
    pub fn as_str(&self) -> &str {
        let Self(inner) = self;
        inner
    }
}
