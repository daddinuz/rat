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

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Word(str);

impl ToOwned for Word {
    type Owned = OwnedWord;

    fn to_owned(&self) -> Self::Owned {
        let Self(word) = self;
        OwnedWord { inner: word.into() }
    }
}

impl Word {
    pub(crate) const fn is_valid(bytes: &[u8], start: usize, end: usize) -> bool {
        if !(start < end && start < bytes.len() && end <= bytes.len()) {
            return false;
        }

        let mut i = start;

        while i < end {
            let c = bytes[i];

            if !(c == b'-' || c.is_ascii_digit() || c == b'_') {
                break;
            }

            i += 1;
        }

        while i < end {
            let c = bytes[i];

            if !c.is_ascii_alphabetic() {
                break;
            }

            i += 1;
        }

        while i < end {
            let c = bytes[i];

            if !(c == b'-' || c.is_ascii_alphanumeric() || c == b'_') {
                break;
            }

            i += 1;
        }

        if i < end {
            let c = bytes[i];

            if c == b'!' || c == b'?' {
                i += 1;
            }
        }

        end == i
    }

    /// Whitespaces are not allowed in `literal`.
    // TODO: this must always be kept in sync with `grammar.pest`
    pub const fn try_from_literal(literal: &str) -> Result<&Self, InvalidWordLiteral> {
        let bytes = literal.as_bytes();

        if Self::is_valid(bytes, 0, bytes.len()) {
            let word = literal as *const str as *const Self;
            // Safety: `Word` is a `repr(transparent)` wrapper around `str`
            // have a look at: https://stackoverflow.com/a/72106272
            return Ok(unsafe { &*word });
        }

        Err(InvalidWordLiteral)
    }

    #[inline]
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl Display for Word {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for Word {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OwnedWord {
    inner: Arc<str>,
}

impl From<&Word> for OwnedWord {
    fn from(word: &Word) -> Self {
        word.to_owned()
    }
}

impl Deref for OwnedWord {
    type Target = Word;

    fn deref(&self) -> &Self::Target {
        self.borrow()
    }
}

impl Borrow<Word> for OwnedWord {
    fn borrow(&self) -> &Word {
        let word = self.inner.as_ref() as *const str as *const Word;
        // Safety: `Word` is a `repr(transparent)` wrapper around `str`
        // have a look at: https://stackoverflow.com/a/72106272
        unsafe { &*word }
    }
}

impl Display for OwnedWord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

impl Debug for OwnedWord {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.as_str())
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InvalidWordLiteral;

impl Display for InvalidWordLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Error for InvalidWordLiteral {}
