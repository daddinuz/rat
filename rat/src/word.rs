/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::borrow::Borrow;
use std::error::Error;
use std::fmt::{Debug, Display};

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Word(str);

impl ToOwned for Word {
    type Owned = OwnedWord;

    fn to_owned(&self) -> Self::Owned {
        let Self(word) = self;
        OwnedWord(word.into())
    }
}

impl Word {
    /// Whitespaces are not allowed in `literal`.
    // TODO: this must always be kept in sync with `grammar.pest`
    pub const fn try_from_literal(literal: &str) -> Result<&Self, InvalidWordLiteral> {
        let bytes = literal.as_bytes();
        if bytes.is_empty() {
            return Err(InvalidWordLiteral);
        }

        let mut i = 0;
        while i < bytes.len() {
            let c = bytes[i];

            if !(b'!' == c
                || b'%' == c
                || b'&' == c
                || b'*' == c
                || b'+' == c
                || b'-' == c
                || b'/' == c
                || b'<' == c
                || b'=' == c
                || b'>' == c
                || b'?' == c
                || (b'A' <= c && b'Z' >= c)
                || b'^' == c
                || b'_' == c
                || (b'a' <= c && b'z' >= c)
                || b'|' == c
                || b'~' == c)
            {
                return Err(InvalidWordLiteral);
            }

            i += 1;
        }

        let word = literal as *const str as *const Self;
        // Safety: `Word` is a `repr(transparent)` wrapper around `str`
        // have a look at: https://stackoverflow.com/a/72106272
        Ok(unsafe { &*word })
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
pub struct OwnedWord(Box<str>);

impl From<&Word> for OwnedWord {
    fn from(word: &Word) -> Self {
        word.to_owned()
    }
}

impl Borrow<Word> for OwnedWord {
    fn borrow(&self) -> &Word {
        let word = self.as_str() as *const str as *const Word;
        // Safety: `Word` is a `repr(transparent)` wrapper around `str`
        // have a look at: https://stackoverflow.com/a/72106272
        unsafe { &*word }
    }
}

impl OwnedWord {
    #[inline]
    pub fn as_str(&self) -> &str {
        &self.0
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
