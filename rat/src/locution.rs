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
pub struct Locution(str);

impl ToOwned for Locution {
    type Owned = OwnedLocution;

    fn to_owned(&self) -> Self::Owned {
        let Self(inner) = self;
        OwnedLocution {
            inner: inner.into(),
        }
    }
}

impl Locution {
    /// Whitespaces are not allowed in `literal`.
    // TODO: this must always be kept in sync with `grammar.pest`
    pub const fn try_from_literal(literal: &str) -> Result<&Self, InvalidLocutionLiteral> {
        let bytes = literal.as_bytes();
        if bytes.is_empty() {
            return Err(InvalidLocutionLiteral);
        }

        let mut start = 0;
        let mut end = 0;
        while end < bytes.len() {
            let c = bytes[end];

            if b'\\' == c {
                if !Word::is_valid(bytes, start, end) {
                    return Err(InvalidLocutionLiteral);
                }

                start = end + 1;
            }

            end += 1;
        }

        if !Word::is_valid(bytes, start, end) {
            return Err(InvalidLocutionLiteral);
        }

        let locution = literal as *const str as *const Self;
        // Safety: `Locution` is a `repr(transparent)` wrapper around `str`
        // have a look at: https://stackoverflow.com/a/72106272
        Ok(unsafe { &*locution })
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    pub fn words(&self) -> impl Iterator<Item = &Word> {
        self.as_str()
            .split('\\')
            .map(|s| Word::try_from_literal(s).unwrap())
    }
}

impl Display for Locution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for Locution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OwnedLocution {
    inner: Arc<str>,
}

impl From<&Locution> for OwnedLocution {
    fn from(locution: &Locution) -> Self {
        locution.to_owned()
    }
}

impl Deref for OwnedLocution {
    type Target = Locution;

    fn deref(&self) -> &Self::Target {
        self.borrow()
    }
}

impl Borrow<Locution> for OwnedLocution {
    fn borrow(&self) -> &Locution {
        let locution = self.inner.as_ref() as *const str as *const Locution;
        // Safety: `Locution` is a `repr(transparent)` wrapper around `str`
        // have a look at: https://stackoverflow.com/a/72106272
        unsafe { &*locution }
    }
}

impl Display for OwnedLocution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for OwnedLocution {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InvalidLocutionLiteral;

impl Display for InvalidLocutionLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Error for InvalidLocutionLiteral {}
