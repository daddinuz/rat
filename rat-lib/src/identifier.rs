/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::borrow::Borrow;
use std::fmt::{Debug, Display};

use crate::component::Component;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Identifier(str);

impl ToOwned for Identifier {
    type Owned = OwnedIdentifier;

    fn to_owned(&self) -> Self::Owned {
        let Self(inner) = self;
        OwnedIdentifier(inner.into())
    }
}

impl Identifier {
    /// Whitespaces are not allowed in `literal`.
    // TODO: this must always be kept in sync with `grammar.pest`
    pub const fn try_from_literal(literal: &str) -> Option<&Self> {
        let bytes = literal.as_bytes();
        if bytes.is_empty() {
            return None;
        }

        let (mut start, mut end) = (0, 0);
        while end < bytes.len() {
            let c = bytes[end];

            if b'/' == c {
                if !Component::is_valid(bytes, start, end) {
                    return None;
                }

                start = end + 1;
            }

            end += 1;
        }

        if !Component::is_valid(bytes, start, end) {
            return None;
        }

        Some(unsafe { Self::new(literal) })
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        let Self(inner) = self;
        inner
    }

    pub fn components(&self) -> impl Iterator<Item = &Component> {
        self.as_str()
            .split('/')
            .map(|s| unsafe { Component::new(s) })
    }

    #[inline]
    pub(crate) const unsafe fn new(literal: &str) -> &Self {
        let inner = literal as *const str as *const Self;
        // Safety: `Component` is a `repr(transparent)` wrapper around `str`
        // have a look at: https://stackoverflow.com/a/72106272
        unsafe { &*inner }
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for Identifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OwnedIdentifier(Box<str>);

impl From<&Identifier> for OwnedIdentifier {
    #[inline]
    fn from(identifier: &Identifier) -> Self {
        identifier.to_owned()
    }
}

impl Borrow<Identifier> for OwnedIdentifier {
    fn borrow(&self) -> &Identifier {
        unsafe { Identifier::new(self.as_str()) }
    }
}

impl Display for OwnedIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for OwnedIdentifier {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

impl OwnedIdentifier {
    #[inline]
    pub fn as_str(&self) -> &str {
        let Self(inner) = self;
        inner
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn components() {
        let sut = Identifier::try_from_literal("a/very/long/identifier").unwrap();
        assert!(sut.components().eq([
            Component::try_from_literal("a").unwrap(),
            Component::try_from_literal("very").unwrap(),
            Component::try_from_literal("long").unwrap(),
            Component::try_from_literal("identifier").unwrap()
        ]));
    }
}
