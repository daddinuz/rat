/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::Debug;

use crate::boolean::Boolean;
use crate::character::Character;
use crate::context::Context;
use crate::decimal::Decimal;
use crate::integer::Integer;
use crate::object::Object;
use crate::symbol::Symbol;
use crate::verb::Verb;

#[derive(Clone)]
#[non_exhaustive]
#[repr(C)]
pub enum Word {
    Boolean(Boolean),
    Character(Character),
    Decimal(Decimal),
    Integer(Integer),
    Symbol(Symbol),
    Verb(Verb),
    Object(Object),
}

const _: () = crate::is_thread_safe::<Word>();
const _: [(); 2 * std::mem::size_of::<usize>()] = [(); std::mem::size_of::<Word>()];

impl Word {
    pub fn apply(self, context: &mut Context) -> Result<(), Symbol> {
        match self {
            Word::Verb(verb) => verb.apply(context),
            _ => {
                context.stack.push(self);
                Ok(())
            }
        }
    }

    pub fn try_into_boolean(self) -> Result<Boolean, Word> {
        match self {
            Word::Boolean(value) => Ok(value),
            _ => Err(self),
        }
    }

    pub fn try_into_character(self) -> Result<Character, Word> {
        match self {
            Word::Character(value) => Ok(value),
            _ => Err(self),
        }
    }

    pub fn try_into_decimal(self) -> Result<Decimal, Word> {
        match self {
            Word::Decimal(value) => Ok(value),
            _ => Err(self),
        }
    }

    pub fn try_into_integer(self) -> Result<Integer, Word> {
        match self {
            Word::Integer(value) => Ok(value),
            _ => Err(self),
        }
    }

    pub fn try_into_symbol(self) -> Result<Symbol, Word> {
        match self {
            Word::Symbol(value) => Ok(value),
            _ => Err(self),
        }
    }

    pub fn try_into_verb(self) -> Result<Verb, Word> {
        match self {
            Word::Verb(value) => Ok(value),
            _ => Err(self),
        }
    }

    pub fn try_into_object(self) -> Result<Object, Word> {
        match self {
            Word::Object(value) => Ok(value),
            _ => Err(self),
        }
    }

    pub fn into_boolean(self) -> Option<Boolean> {
        match self {
            Word::Boolean(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_character(self) -> Option<Character> {
        match self {
            Word::Character(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_decimal(self) -> Option<Decimal> {
        match self {
            Word::Decimal(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_integer(self) -> Option<Integer> {
        match self {
            Word::Integer(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_symbol(self) -> Option<Symbol> {
        match self {
            Word::Symbol(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_verb(self) -> Option<Verb> {
        match self {
            Word::Verb(value) => Some(value),
            _ => None,
        }
    }

    pub fn into_object(self) -> Option<Object> {
        match self {
            Word::Object(value) => Some(value),
            _ => None,
        }
    }

    pub const fn as_boolean(&self) -> Option<Boolean> {
        match self {
            Word::Boolean(value) => Some(*value),
            _ => None,
        }
    }

    pub const fn as_character(&self) -> Option<Character> {
        match self {
            Word::Character(value) => Some(*value),
            _ => None,
        }
    }

    pub const fn as_decimal(&self) -> Option<Decimal> {
        match self {
            Word::Decimal(value) => Some(*value),
            _ => None,
        }
    }

    pub const fn as_integer(&self) -> Option<Integer> {
        match self {
            Word::Integer(value) => Some(*value),
            _ => None,
        }
    }

    pub const fn as_symbol(&self) -> Option<Symbol> {
        match self {
            Word::Symbol(value) => Some(*value),
            _ => None,
        }
    }

    pub const fn as_verb(&self) -> Option<Verb> {
        match self {
            Word::Verb(value) => Some(*value),
            _ => None,
        }
    }

    pub const fn as_object(&self) -> Option<&Object> {
        match self {
            Word::Object(value) => Some(value),
            _ => None,
        }
    }

    pub const fn as_boolean_mut(&mut self) -> Option<&mut Boolean> {
        match self {
            Word::Boolean(value) => Some(value),
            _ => None,
        }
    }

    pub const fn as_character_mut(&mut self) -> Option<&mut Character> {
        match self {
            Word::Character(value) => Some(value),
            _ => None,
        }
    }

    pub const fn as_decimal_mut(&mut self) -> Option<&mut Decimal> {
        match self {
            Word::Decimal(value) => Some(value),
            _ => None,
        }
    }

    pub const fn as_integer_mut(&mut self) -> Option<&mut Integer> {
        match self {
            Word::Integer(value) => Some(value),
            _ => None,
        }
    }

    pub const fn as_symbol_mut(&mut self) -> Option<&mut Symbol> {
        match self {
            Word::Symbol(value) => Some(value),
            _ => None,
        }
    }

    pub const fn as_verb_mut(&mut self) -> Option<&mut Verb> {
        match self {
            Word::Verb(value) => Some(value),
            _ => None,
        }
    }

    pub const fn as_object_mut(&mut self) -> Option<&mut Object> {
        match self {
            Word::Object(value) => Some(value),
            _ => None,
        }
    }
}

impl Debug for Word {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Word::Boolean(boolean) => Debug::fmt(boolean, f),
            Word::Character(character) => Debug::fmt(character, f),
            Word::Decimal(decimal) => Debug::fmt(decimal, f),
            Word::Integer(integer) => Debug::fmt(integer, f),
            Word::Symbol(symbol) => Debug::fmt(symbol, f),
            Word::Verb(verb) => Debug::fmt(verb, f),
            Word::Object(object) => Debug::fmt(object, f),
        }
    }
}
