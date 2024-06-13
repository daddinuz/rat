/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::borrow::Borrow;
use std::error::Error;
use std::fmt::{Debug, Display};
use std::ops::Deref;
use std::sync::Arc;

use crate::word::Word;

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Identifier(str);

impl ToOwned for Identifier {
    type Owned = OwnedIdentifier;

    fn to_owned(&self) -> Self::Owned {
        let Self(inner) = self;
        OwnedIdentifier {
            inner: inner.into(),
        }
    }
}

impl Identifier {
    /// Whitespaces are not allowed in `literal`.
    // TODO: this must always be kept in sync with `grammar.pest`
    pub const fn try_from_literal(literal: &str) -> Result<&Self, InvalidIdentifierLiteral> {
        let bytes = literal.as_bytes();
        if bytes.is_empty() {
            return Err(InvalidIdentifierLiteral);
        }

        let mut start = 0;
        let mut end = 0;
        while end < bytes.len() {
            let c = bytes[end];

            if b'/' == c {
                if !Word::is_valid(bytes, start, end) {
                    return Err(InvalidIdentifierLiteral);
                }

                start = end + 1;
            }

            end += 1;
        }

        if !Word::is_valid(bytes, start, end) {
            return Err(InvalidIdentifierLiteral);
        }

        let identifier = literal as *const str as *const Self;
        // Safety: `Identifier` is a `repr(transparent)` wrapper around `str`
        // have a look at: https://stackoverflow.com/a/72106272
        Ok(unsafe { &*identifier })
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn words(&self) -> impl Iterator<Item = &Word> {
        self.as_str()
            .split('/')
            .map(|s| Word::try_from_literal(s).unwrap())
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
pub struct OwnedIdentifier {
    inner: Arc<str>,
}

impl From<&Identifier> for OwnedIdentifier {
    fn from(identifier: &Identifier) -> Self {
        identifier.to_owned()
    }
}

impl Deref for OwnedIdentifier {
    type Target = Identifier;

    fn deref(&self) -> &Self::Target {
        self.borrow()
    }
}

impl Borrow<Identifier> for OwnedIdentifier {
    fn borrow(&self) -> &Identifier {
        let identifier = self.inner.as_ref() as *const str as *const Identifier;
        // Safety: `Identifier` is a `repr(transparent)` wrapper around `str`
        // have a look at: https://stackoverflow.com/a/72106272
        unsafe { &*identifier }
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InvalidIdentifierLiteral;

impl Display for InvalidIdentifierLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Error for InvalidIdentifierLiteral {}

#[cfg(test)]
mod test {
    use crate::word::Word;

    use super::Identifier;

    #[test]
    fn identifier_words() {
        let sut = Identifier::try_from_literal("a/very/long/identifier").unwrap();
        assert!(sut.words().eq([
            Word::try_from_literal("a").unwrap(),
            Word::try_from_literal("very").unwrap(),
            Word::try_from_literal("long").unwrap(),
            Word::try_from_literal("identifier").unwrap()
        ]
        .into_iter()));
    }
}
