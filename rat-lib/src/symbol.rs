/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};
use std::sync::LazyLock;
use std::sync::Mutex;

use hashbrown::{Equivalent, HashSet};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Symbol(&'static &'static str);

#[allow(non_upper_case_globals)]
impl Symbol {
    // Effects
    pub const Break: Self = Self(BREAK_LITERAL);
    pub const Continue: Self = Self(CONTINUE_LITERAL);
    pub const Yield: Self = Self(YIELD_LITERAL);
    pub const Recur: Self = Self(RECUR_LITERAL);
    pub const Return: Self = Self(RETURN_LITERAL);
    pub const Throw: Self = Self(THROW_LITERAL);
    // Errors
    pub const IOError: Self = Self(IO_ERROR_LITERAL);
    pub const TypeError: Self = Self(TYPE_ERROR_LITERAL);
    pub const RangeError: Self = Self(RANGE_ERROR_LITERAL);
    pub const DomainError: Self = Self(DOMAIN_ERROR_LITERAL);
    pub const LayoutError: Self = Self(LAYOUT_ERROR_LITERAL);
    pub const EffectError: Self = Self(EFFECT_ERROR_LITERAL);
}

impl Symbol {
    pub fn intern(s: &str) -> Symbol {
        let mut table = TABLE.lock().unwrap();
        let atom = table.get_or_insert_with(&Holder(s), |_| {
            let s: Box<str> = s.into();
            let s: &'static str = Box::leak(s);
            let s: Box<&'static str> = Box::new(s);
            Box::leak(s)
        });

        Symbol(atom)
    }

    pub fn intern_static(s: &'static str) -> Symbol {
        let mut table = TABLE.lock().unwrap();
        let atom = table.get_or_insert_with(&Holder(s), |_| {
            let s: Box<&'static str> = Box::new(s);
            Box::leak(s)
        });

        Symbol(atom)
    }
}

impl Debug for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let &Self(&id) = self;
        write!(f, "${id:?}")
    }
}

impl Display for Symbol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

// Effects
static BREAK_LITERAL: &'static &str = &"Break";
static CONTINUE_LITERAL: &'static &str = &"Continue";
static YIELD_LITERAL: &'static &str = &"Yield";
static RECUR_LITERAL: &'static &str = &"Recur";
static RETURN_LITERAL: &'static &str = &"Return";
static THROW_LITERAL: &'static &str = &"Throw";

// Errors
static IO_ERROR_LITERAL: &'static &str = &"IOError";
static TYPE_ERROR_LITERAL: &'static &str = &"TypeError";
static RANGE_ERROR_LITERAL: &'static &str = &"RangeError";
static DOMAIN_ERROR_LITERAL: &'static &str = &"DomainError";
static LAYOUT_ERROR_LITERAL: &'static &str = &"LayoutError";
static EFFECT_ERROR_LITERAL: &'static &str = &"EffectError";

static TABLE: LazyLock<Mutex<HashSet<&'static &'static str>>> = LazyLock::new(|| {
    let set = [
        // Effects
        BREAK_LITERAL,
        CONTINUE_LITERAL,
        YIELD_LITERAL,
        RECUR_LITERAL,
        RETURN_LITERAL,
        THROW_LITERAL,
        // Errors
        IO_ERROR_LITERAL,
        TYPE_ERROR_LITERAL,
        RANGE_ERROR_LITERAL,
        DOMAIN_ERROR_LITERAL,
        LAYOUT_ERROR_LITERAL,
        EFFECT_ERROR_LITERAL,
    ]
    .into_iter()
    .collect();

    Mutex::new(set)
});

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Holder<'a>(&'a str);

impl Equivalent<&'static &'static str> for Holder<'_> {
    fn equivalent(&self, key: &&'static &'static str) -> bool {
        *key == &self.0
    }
}
