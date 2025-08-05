/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use crate::object::Object;
use crate::quote::Quote;
use crate::symbol::Symbol;
use crate::verb::Verb;
use crate::word::Word;

#[derive(Debug, Default)]
pub struct Context {
    pub stack: Vec<Word>,
    pub continuation: Quote,
}

impl Context {
    pub const fn new() -> Self {
        Self {
            stack: Vec::new(),
            continuation: Quote::new(),
        }
    }

    // TODO: add documentation about effect handling
    pub fn unquote(&mut self, quote: &Quote) -> Result<(), Symbol> {
        let mut continuation = quote.iter().cloned();
        continuation
            .try_for_each(|word| word.apply(self))
            .inspect_err(|_| self.continuation.extend(continuation))
    }

    // TODO: add documentation about effect handling
    pub fn apply(&mut self, quote: &Quote) -> Result<(), Symbol> {
        self.apply_recursive(quote, quote)
    }

    // TODO: add documentation about effect handling
    pub fn apply_recursive(&mut self, recur: &Quote, quote: &Quote) -> Result<(), Symbol> {
        match self.unquote(quote) {
            // cannot break/continue from a function
            Err(effect @ (Symbol::Break | Symbol::Continue)) => {
                self.continuation.clear();

                self.stack
                    .extend_from_slice(&[Word::Symbol(effect), Word::Symbol(Symbol::EffectError)]);

                Err(Symbol::Throw)
            }
            // push the current continuation on the stack and exit
            Err(Symbol::Yield) => {
                let continuation = std::mem::take(&mut self.continuation);

                self.stack.push(Word::Object(Object::new(Quote::from([
                    Word::Object(Object::new(recur.clone())),
                    Word::Object(Object::new(continuation)),
                    Word::Verb(Verb(crate::prelude::r)),
                ]))));

                Ok(())
            }
            // apply recursive call and then resume what's left
            Err(Symbol::Recur) => {
                let mut continuation = std::mem::take(&mut self.continuation);
                self.apply_recursive(recur, recur)?;
                continuation.extend(std::mem::take(&mut self.continuation));
                self.apply_recursive(recur, &continuation)
            }
            // early exit requested so discard the current continuation and exit
            Err(Symbol::Return) => {
                self.continuation.clear();
                Ok(())
            }
            // let other effects float to the layers above so that other functions in the call stack can handle them
            // e.g. throw
            effect => effect,
        }
    }

    // TODO: add documentation about effect handling
    pub fn apply_sealed(&mut self, quote: &Quote) -> Result<(), Symbol> {
        if let Err(effect) = quote.iter().cloned().try_for_each(|word| word.apply(self)) {
            self.continuation.clear();
            self.stack
                .extend_from_slice(&[Word::Symbol(effect), Word::Symbol(Symbol::EffectError)]);

            return Err(Symbol::Throw);
        }

        Ok(())
    }
}
