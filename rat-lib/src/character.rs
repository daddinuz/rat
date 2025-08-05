/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};

#[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
pub struct Character(pub char);

impl From<char> for Character {
    #[inline]
    fn from(value: char) -> Self {
        Self(value)
    }
}

impl From<Character> for char {
    #[inline]
    fn from(Character(value): Character) -> Self {
        value
    }
}

impl Debug for Character {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(c) = self;
        write!(f, "'{}'", c.escape_debug())
    }
}

impl Display for Character {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(c) = self;
        write!(f, "{c}")
    }
}
