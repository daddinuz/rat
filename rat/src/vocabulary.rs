/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::borrow::Borrow;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;
use std::sync::Arc;

use crate::boolean::Boolean;
use crate::builtin;
use crate::decimal::Decimal;
use crate::expression::Expression;
use crate::locution::Locution;
use crate::verb::Verb;
use crate::word::{OwnedWord, Word};

#[derive(Debug)]
pub enum Definition {
    Phrase {
        phrase: Arc<[Expression]>,
        visibility: Visibility,
    },
    Vocabulary {
        vocabulary: Arc<Vocabulary>,
        visibility: Visibility,
    },
}

impl Definition {
    pub fn is_intern(&self) -> bool {
        Visibility::Intern
            == match self {
                Definition::Phrase { visibility, .. } => *visibility,
                Definition::Vocabulary { visibility, .. } => *visibility,
            }
    }

    pub fn is_extern(&self) -> bool {
        !self.is_intern()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Visibility {
    Extern,
    Intern,
}

#[derive(Debug, Default)]
pub struct Vocabulary {
    definitions: HashMap<OwnedWord, Definition>,
}

impl Vocabulary {
    pub fn new() -> Self {
        Self {
            definitions: HashMap::new(),
        }
    }

    pub fn with_prelude() -> Self {
        Self {
            definitions: PRELUDE
                .into_iter()
                .map(|(word, phrase)| {
                    (
                        word.into(),
                        Definition::Phrase {
                            phrase: phrase.into(),
                            visibility: Visibility::Intern,
                        },
                    )
                })
                .collect(),
        }
    }

    pub fn define(&mut self, word: OwnedWord, definition: Definition) -> Option<Definition> {
        self.definitions.insert(word, definition)
    }

    pub fn get<W>(&self, word: &W) -> Option<&Definition>
    where
        OwnedWord: Borrow<W>,
        W: ?Sized + Eq + Hash,
    {
        self.definitions.get(word)
    }

    pub fn lookup(&self, locution: &Locution) -> Option<&[Expression]> {
        let mut words = locution.words();
        let mut vocabulary = self;
        let mut is_first_word = true;

        while let Some(word) = words.next() {
            let definition = vocabulary.get(word)?;

            if !is_first_word && definition.is_intern() {
                break;
            }

            match definition {
                Definition::Phrase { phrase, .. } => {
                    if words.next().is_some() {
                        break;
                    }

                    return Some(phrase);
                }
                Definition::Vocabulary {
                    vocabulary: next_vocabulary,
                    ..
                } => vocabulary = next_vocabulary,
            }

            is_first_word = false;
        }

        None
    }

    pub fn definitions(&self) -> impl Iterator<Item = (&OwnedWord, &Definition)> {
        self.definitions.iter()
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&Word, &Definition) -> bool,
    {
        self.definitions.retain(|w, d| f(w, d));
    }
}

static PRELUDE: [(&Word, &[Expression]); 64] = [
    (word_literal("neg"), &[Expression::Verb(Verb(builtin::neg))]),
    (
        word_literal("incr"),
        &[Expression::Verb(Verb(builtin::incr))],
    ),
    (
        word_literal("decr"),
        &[Expression::Verb(Verb(builtin::decr))],
    ),
    (word_literal("+"), &[Expression::Verb(Verb(builtin::add))]),
    (word_literal("-"), &[Expression::Verb(Verb(builtin::sub))]),
    (word_literal("*"), &[Expression::Verb(Verb(builtin::mul))]),
    (word_literal("/"), &[Expression::Verb(Verb(builtin::div))]),
    (word_literal("%"), &[Expression::Verb(Verb(builtin::rem))]),
    (word_literal("="), &[Expression::Verb(Verb(builtin::eq))]),
    (word_literal("<>"), &[Expression::Verb(Verb(builtin::ne))]),
    (word_literal(">"), &[Expression::Verb(Verb(builtin::gt))]),
    (word_literal(">="), &[Expression::Verb(Verb(builtin::ge))]),
    (word_literal("<"), &[Expression::Verb(Verb(builtin::lt))]),
    (word_literal("<="), &[Expression::Verb(Verb(builtin::le))]),
    (
        word_literal("positive?"),
        &[Expression::Verb(Verb(builtin::positive))],
    ),
    (
        word_literal("zero?"),
        &[Expression::Verb(Verb(builtin::zero))],
    ),
    (
        word_literal("negative?"),
        &[Expression::Verb(Verb(builtin::negative))],
    ),
    (word_literal("nan"), &[Expression::Decimal(Decimal::NAN)]),
    (
        word_literal("inf"),
        &[Expression::Decimal(Decimal::INFINITY)],
    ),
    (
        word_literal("-inf"),
        &[Expression::Decimal(Decimal::NEG_INFINITY)],
    ),
    (
        word_literal("false"),
        &[Expression::Boolean(Boolean(false))],
    ),
    (word_literal("true"), &[Expression::Boolean(Boolean(true))]),
    (word_literal("not"), &[Expression::Verb(Verb(builtin::not))]),
    (word_literal("and"), &[Expression::Verb(Verb(builtin::and))]),
    (word_literal("or"), &[Expression::Verb(Verb(builtin::or))]),
    (
        word_literal("~"),
        &[Expression::Verb(Verb(builtin::bitwise_not))],
    ),
    (
        word_literal("&"),
        &[Expression::Verb(Verb(builtin::bitwise_and))],
    ),
    (
        word_literal("^"),
        &[Expression::Verb(Verb(builtin::bitwise_xor))],
    ),
    (
        word_literal("|"),
        &[Expression::Verb(Verb(builtin::bitwise_or))],
    ),
    (word_literal("<<"), &[Expression::Verb(Verb(builtin::shl))]),
    (word_literal(">>"), &[Expression::Verb(Verb(builtin::shr))]),
    (
        word_literal(">>>"),
        &[Expression::Verb(Verb(builtin::ushr))],
    ),
    (word_literal("cat"), &[Expression::Verb(Verb(builtin::cat))]),
    (
        word_literal("quote"),
        &[Expression::Verb(Verb(builtin::quote))],
    ),
    (
        word_literal("unquote"),
        &[Expression::Verb(Verb(builtin::unquote))],
    ),
    (
        word_literal("eval"),
        &[Expression::Verb(Verb(builtin::eval))],
    ),
    (word_literal("i"), &[Expression::Verb(Verb(builtin::i))]),
    (word_literal("x"), &[Expression::Verb(Verb(builtin::x))]),
    (word_literal("dip"), &[Expression::Verb(Verb(builtin::dip))]),
    (word_literal("if"), &[Expression::Verb(Verb(builtin::r#if))]),
    (
        word_literal("else"),
        &[Expression::Verb(Verb(builtin::r#else))],
    ),
    (
        word_literal("ifElse"),
        &[Expression::Verb(Verb(builtin::if_else))],
    ),
    (
        word_literal("yield"),
        &[Expression::Verb(Verb(builtin::r#yield))],
    ),
    (
        word_literal("raise"),
        &[Expression::Verb(Verb(builtin::raise))],
    ),
    (
        word_literal("catch"),
        &[Expression::Verb(Verb(builtin::catch))],
    ),
    (
        word_literal("first"),
        &[Expression::Verb(Verb(builtin::first))],
    ),
    (
        word_literal("last"),
        &[Expression::Verb(Verb(builtin::last))],
    ),
    (
        word_literal("head"),
        &[Expression::Verb(Verb(builtin::head))],
    ),
    (
        word_literal("tail"),
        &[Expression::Verb(Verb(builtin::tail))],
    ),
    (
        word_literal("swap"),
        &[Expression::Verb(Verb(builtin::swap))],
    ),
    (
        word_literal("rollup"),
        &[Expression::Verb(Verb(builtin::rollup))],
    ),
    (
        word_literal("rolldown"),
        &[Expression::Verb(Verb(builtin::rolldown))],
    ),
    (
        word_literal("rotate"),
        &[Expression::Verb(Verb(builtin::rotate))],
    ),
    (word_literal("pop"), &[Expression::Verb(Verb(builtin::pop))]),
    (word_literal("dup"), &[Expression::Verb(Verb(builtin::dup))]),
    (
        word_literal("send"),
        &[Expression::Verb(Verb(builtin::send))],
    ),
    (
        word_literal("receive"),
        &[Expression::Verb(Verb(builtin::receive))],
    ),
    (
        word_literal("produce"),
        &[Expression::Verb(Verb(builtin::produce))],
    ),
    (
        word_literal("consume"),
        &[Expression::Verb(Verb(builtin::consume))],
    ),
    (
        word_literal("spawn"),
        &[Expression::Verb(Verb(builtin::spawn))],
    ),
    (word_literal("ask"), &[Expression::Verb(Verb(builtin::ask))]),
    (word_literal("say"), &[Expression::Verb(Verb(builtin::say))]),
    (
        word_literal("show"),
        &[Expression::Verb(Verb(builtin::show))],
    ),
    (
        word_literal("binrec"),
        &[Expression::Verb(Verb(builtin::binrec))],
    ),
];

const fn word_literal(literal: &str) -> &Word {
    match Word::try_from_literal(literal) {
        Ok(word) => word,
        Err(_) => panic!("invalid word literal"),
    }
}
