/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::io::{self, Write};
use std::sync::Arc;

use hashbrown::HashMap;

use crate::boolean::Boolean;
use crate::component::Component;
use crate::context::Context;
use crate::decimal::Decimal;
use crate::definition::Definition;
use crate::dictionary::Dictionary;
use crate::integer::Integer;
use crate::object::Object;
use crate::quote::Quote;
use crate::string::String;
use crate::symbol::Symbol;
use crate::verb::Verb;
use crate::visibility::Visibility;
use crate::word::Word;

pub fn neg(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(ref mut v)] => *v = !*v,
        [.., Word::Decimal(ref mut v)] => *v = -*v,
        [.., Word::Integer(ref mut v)] => *v = -*v,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn incr(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Decimal(ref mut lhs)] => *lhs += Decimal::ONE,
        [.., Word::Integer(ref mut lhs)] => *lhs += Integer::ONE,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn decr(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Decimal(ref mut lhs)] => *lhs -= Decimal::ONE,
        [.., Word::Integer(ref mut lhs)] => *lhs -= Integer::ONE,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn add(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Decimal(ref mut lhs), Word::Decimal(rhs)] => *lhs += rhs,
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs += rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn sub(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Decimal(ref mut lhs), Word::Decimal(rhs)] => *lhs -= rhs,
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs -= rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn mul(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Decimal(ref mut lhs), Word::Decimal(rhs)] => *lhs *= rhs,
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs *= rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn div(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Decimal(ref mut lhs), Word::Decimal(rhs)] => *lhs /= rhs,
        [.., Word::Integer(_), Word::Integer(Integer(0))] => {
            context.stack.push(Word::Symbol(Symbol::DomainError));
            return Err(Symbol::Throw);
        }
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs /= rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn rem(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Decimal(ref mut lhs), Word::Decimal(rhs)] => *lhs %= rhs,
        [.., Word::Integer(_), Word::Integer(Integer(0))] => {
            context.stack.push(Word::Symbol(Symbol::DomainError));
            return Err(Symbol::Throw);
        }
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs %= rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn is_eq(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(lhs), ref mut w @ Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        [.., Word::Character(lhs), ref mut w @ Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        [.., Word::Decimal(lhs), ref mut w @ Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        [.., Word::Integer(lhs), ref mut w @ Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        [.., Word::Symbol(lhs), ref mut w @ Word::Symbol(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn is_ne(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(lhs), ref mut w @ Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        [.., Word::Character(lhs), ref mut w @ Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        [.., Word::Decimal(lhs), ref mut w @ Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        [.., Word::Integer(lhs), ref mut w @ Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        [.., Word::Symbol(lhs), ref mut w @ Word::Symbol(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn is_gt(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(lhs), ref mut w @ Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs > rhs))
        }
        [.., Word::Character(lhs), ref mut w @ Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs > rhs))
        }
        [.., Word::Decimal(lhs), ref mut w @ Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs > rhs))
        }
        [.., Word::Integer(lhs), ref mut w @ Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs > rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn is_ge(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(lhs), ref mut w @ Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs >= rhs))
        }
        [.., Word::Character(lhs), ref mut w @ Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs >= rhs))
        }
        [.., Word::Decimal(lhs), ref mut w @ Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs >= rhs))
        }
        [.., Word::Integer(lhs), ref mut w @ Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs >= rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn is_lt(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(lhs), ref mut w @ Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs < rhs))
        }
        [.., Word::Character(lhs), ref mut w @ Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs < rhs))
        }
        [.., Word::Decimal(lhs), ref mut w @ Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs < rhs))
        }
        [.., Word::Integer(lhs), ref mut w @ Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs < rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn is_le(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(lhs), ref mut w @ Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs <= rhs))
        }
        [.., Word::Character(lhs), ref mut w @ Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs <= rhs))
        }
        [.., Word::Decimal(lhs), ref mut w @ Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs <= rhs))
        }
        [.., Word::Integer(lhs), ref mut w @ Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs <= rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn bang_is_eq(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., ref mut w @ Word::Boolean(lhs), Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        [.., ref mut w @ Word::Character(lhs), Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        [.., ref mut w @ Word::Decimal(lhs), Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        [.., ref mut w @ Word::Integer(lhs), Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        [.., ref mut w @ Word::Symbol(lhs), Word::Symbol(rhs)] => {
            *w = Word::Boolean(Boolean(lhs == rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn bang_is_ne(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., ref mut w @ Word::Boolean(lhs), Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        [.., ref mut w @ Word::Character(lhs), Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        [.., ref mut w @ Word::Decimal(lhs), Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        [.., ref mut w @ Word::Integer(lhs), Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        [.., ref mut w @ Word::Symbol(lhs), Word::Symbol(rhs)] => {
            *w = Word::Boolean(Boolean(lhs != rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn bang_is_gt(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., ref mut w @ Word::Boolean(lhs), Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs > rhs))
        }
        [.., ref mut w @ Word::Character(lhs), Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs > rhs))
        }
        [.., ref mut w @ Word::Decimal(lhs), Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs > rhs))
        }
        [.., ref mut w @ Word::Integer(lhs), Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs > rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn bang_is_ge(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., ref mut w @ Word::Boolean(lhs), Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs >= rhs))
        }
        [.., ref mut w @ Word::Character(lhs), Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs >= rhs))
        }
        [.., ref mut w @ Word::Decimal(lhs), Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs >= rhs))
        }
        [.., ref mut w @ Word::Integer(lhs), Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs >= rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn bang_is_lt(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., ref mut w @ Word::Boolean(lhs), Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs < rhs))
        }
        [.., ref mut w @ Word::Character(lhs), Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs < rhs))
        }
        [.., ref mut w @ Word::Decimal(lhs), Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs < rhs))
        }
        [.., ref mut w @ Word::Integer(lhs), Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs < rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn bang_is_le(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., ref mut w @ Word::Boolean(lhs), Word::Boolean(rhs)] => {
            *w = Word::Boolean(Boolean(lhs <= rhs))
        }
        [.., ref mut w @ Word::Character(lhs), Word::Character(rhs)] => {
            *w = Word::Boolean(Boolean(lhs <= rhs))
        }
        [.., ref mut w @ Word::Decimal(lhs), Word::Decimal(rhs)] => {
            *w = Word::Boolean(Boolean(lhs <= rhs))
        }
        [.., ref mut w @ Word::Integer(lhs), Word::Integer(rhs)] => {
            *w = Word::Boolean(Boolean(lhs <= rhs))
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn not(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(ref mut v)] => *v = !*v,
        [.., Word::Integer(ref mut v)] => *v = !*v,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn and(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(ref mut lhs), Word::Boolean(rhs)] => *lhs &= rhs,
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs &= rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn xor(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(ref mut lhs), Word::Boolean(rhs)] => *lhs ^= rhs,
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs ^= rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn or(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(ref mut lhs), Word::Boolean(rhs)] => *lhs |= rhs,
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs |= rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn shl(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs <<= rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn shr(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs >>= rhs,
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn ushr(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Integer(ref mut lhs), Word::Integer(rhs)] => *lhs = lhs.ushr(rhs),
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn replace(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref mut list_object),
            ref mut word,
            Word::Integer(Integer(index)),
        ] if list_object.is::<Quote>() => {
            let list = list_object.make_mut::<Quote>().unwrap();

            let index = if index >= 0 {
                usize::try_from(index).map_err(|_| Symbol::RangeError)?
            } else {
                list.len()
                    - usize::try_from(index.unsigned_abs()).map_err(|_| Symbol::RangeError)?
            };

            match list.get_mut(index) {
                None => {
                    context.stack.push(Word::Symbol(Symbol::RangeError));
                    Err(Symbol::Throw)
                }
                Some(lhs) => {
                    std::mem::swap(lhs, word);
                    context.stack.pop();
                    Ok(())
                }
            }
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn set(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref mut list_object),
            ref mut word,
            Word::Integer(Integer(index)),
        ] if list_object.is::<Quote>() => {
            let list = list_object.make_mut::<Quote>().unwrap();

            let index = if index >= 0 {
                usize::try_from(index).map_err(|_| Symbol::RangeError)?
            } else {
                list.len()
                    - usize::try_from(index.unsigned_abs()).map_err(|_| Symbol::RangeError)?
            };

            match list.get_mut(index) {
                None => {
                    context.stack.push(Word::Symbol(Symbol::RangeError));
                    Err(Symbol::Throw)
                }
                Some(lhs) => {
                    std::mem::swap(lhs, word);
                    context.stack.truncate(context.stack.len() - 2);
                    Ok(())
                }
            }
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn get(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref list_object),
            Word::Integer(Integer(index)),
        ] if list_object.is::<Quote>() => {
            let list = list_object.downcast_ref::<Quote>().unwrap();

            let index = if index >= 0 {
                usize::try_from(index).map_err(|_| Symbol::RangeError)?
            } else {
                list.len()
                    - usize::try_from(index.unsigned_abs()).map_err(|_| Symbol::RangeError)?
            };

            *context.stack.last_mut().unwrap() = list.get(index).cloned().ok_or_else(|| {
                context.stack.push(Word::Symbol(Symbol::RangeError));
                Symbol::Throw
            })?;

            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn bang_get(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref list_object),
            Word::Integer(Integer(index)),
        ] if list_object.is::<Quote>() => {
            let list = list_object.downcast_ref::<Quote>().unwrap();

            let index = if index >= 0 {
                usize::try_from(index).map_err(|_| Symbol::RangeError)?
            } else {
                list.len()
                    - usize::try_from(index.unsigned_abs()).map_err(|_| Symbol::RangeError)?
            };

            let word = list.get(index).cloned().ok_or_else(|| {
                context.stack.push(Word::Symbol(Symbol::RangeError));
                Symbol::Throw
            })?;

            context.stack.pop();
            *context.stack.last_mut().unwrap() = word;

            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn get_or_else(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref list_object),
            Word::Integer(Integer(index)),
            _,
        ] if list_object.is::<Quote>() => {
            let list = list_object.downcast_ref::<Quote>().unwrap();

            let index = if index >= 0 {
                usize::try_from(index).map_err(|_| Symbol::RangeError)?
            } else {
                list.len()
                    - usize::try_from(index.unsigned_abs()).map_err(|_| Symbol::RangeError)?
            };

            match list.get(index) {
                Some(word) => {
                    let word = word.clone();
                    context.stack.pop();
                    *context.stack.last_mut().unwrap() = word;
                }
                None => {
                    let word = context.stack.pop().unwrap();
                    *context.stack.last_mut().unwrap() = word;
                }
            }

            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn shallow_bind(context: &mut Context) -> Result<(), Symbol> {
    let stack_len = context.stack.len();

    match context.stack[..] {
        [
            ..,
            ref word,
            Word::Object(ref mut quote_object),
            Word::Symbol(key),
        ] if quote_object.is::<Quote>() => {
            let quote = quote_object.make_mut::<Quote>().unwrap();

            for w in quote.iter_mut() {
                match w {
                    Word::Symbol(symbol) if *symbol == key => *w = word.clone(),
                    _ => (),
                }
            }

            context.stack.swap(stack_len - 3, stack_len - 2);
            context.stack.truncate(stack_len - 2);
            Ok(())
        }
        [
            ..,
            Word::Object(ref pattern_object),
            Word::Object(ref capture_object),
        ] if pattern_object.is::<Quote>() && capture_object.is::<Quote>() => {
            let capture = capture_object.downcast_ref::<Quote>().unwrap();
            if capture.len() > stack_len - 2
                || capture.iter().any(|w| !matches!(w, Word::Symbol(_)))
            {
                context.stack.push(Word::Symbol(Symbol::LayoutError));
                return Err(Symbol::Throw);
            }

            let capture_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let mut pattern_object = context.stack.pop().and_then(Word::into_object).unwrap();

            let stack_len = context.stack.len();
            let capture = capture_object.downcast_ref::<Quote>().unwrap();
            let pattern = pattern_object.make_mut::<Quote>().unwrap();

            let bindings: HashMap<Symbol, Word> = capture
                .into_iter()
                .map(|w| w.as_symbol().unwrap())
                .zip(context.stack.drain(stack_len - capture.len()..))
                .collect();

            for w in pattern.iter_mut() {
                if let Word::Symbol(symbol) = w
                    && let Some(word) = bindings.get(symbol)
                {
                    *w = word.clone();
                }
            }

            context.stack.push(Word::Object(pattern_object));
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn deep_bind(context: &mut Context) -> Result<(), Symbol> {
    let stack_len = context.stack.len();

    match context.stack[..] {
        [
            ..,
            ref word,
            Word::Object(ref mut quote_object),
            Word::Symbol(key),
        ] if quote_object.is::<Quote>() => {
            let quote = quote_object.make_mut::<Quote>().unwrap();
            deep_bind_one_aux(quote, key, word);

            context.stack.swap(stack_len - 3, stack_len - 2);
            context.stack.truncate(stack_len - 2);
            Ok(())
        }
        [
            ..,
            Word::Object(ref pattern_object),
            Word::Object(ref capture_object),
        ] if pattern_object.is::<Quote>() && capture_object.is::<Quote>() => {
            let capture = capture_object.downcast_ref::<Quote>().unwrap();
            if capture.len() > stack_len - 2
                || capture.iter().any(|w| !matches!(w, Word::Symbol(_)))
            {
                context.stack.push(Word::Symbol(Symbol::LayoutError));
                return Err(Symbol::Throw);
            }

            let capture_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let mut pattern_object = context.stack.pop().and_then(Word::into_object).unwrap();

            let stack_len = context.stack.len();
            let capture = capture_object.downcast_ref::<Quote>().unwrap();
            let pattern = pattern_object.make_mut::<Quote>().unwrap();

            let bindings: HashMap<Symbol, Word> = capture
                .into_iter()
                .map(|w| w.as_symbol().unwrap())
                .zip(context.stack.drain(stack_len - capture.len()..))
                .collect();

            deep_bind_many_aux(pattern, &bindings);

            context.stack.push(Word::Object(pattern_object));
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

fn deep_bind_one_aux(quote: &mut Quote, key: Symbol, word: &Word) {
    for w in quote.iter_mut() {
        match w {
            Word::Symbol(symbol) if *symbol == key => *w = word.clone(),
            Word::Object(object) if object.is::<Quote>() => {
                deep_bind_one_aux(object.make_mut::<Quote>().unwrap(), key, word)
            }
            _ => (),
        }
    }
}

fn deep_bind_many_aux(quote: &mut Quote, bindings: &HashMap<Symbol, Word>) {
    for w in quote.iter_mut() {
        match w {
            Word::Symbol(symbol) => {
                if let Some(word) = bindings.get(symbol) {
                    *w = word.clone();
                }
            }
            Word::Object(object) if object.is::<Quote>() => {
                deep_bind_many_aux(object.make_mut::<Quote>().unwrap(), bindings)
            }
            _ => (),
        }
    }
}

pub fn quote(context: &mut Context) -> Result<(), Symbol> {
    let word = context.stack.pop().ok_or_else(|| {
        context.stack.push(Word::Symbol(Symbol::LayoutError));
        Symbol::Throw
    })?;

    let quote = Quote::from([word]);
    context.stack.push(Word::Object(Object::new(quote)));
    Ok(())
}

pub fn unquote(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Object(ref quote_object)] if quote_object.is::<Quote>() => {
            let quote_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let quote = quote_object.downcast_ref::<Quote>().unwrap();
            context.unquote(quote)
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn cat(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Object(ref mut lhs), Word::Object(ref rhs)]
            if lhs.is::<Quote>() && rhs.is::<Quote>() =>
        {
            let rhs = rhs.downcast_ref::<Quote>().unwrap();
            let lhs = lhs.make_mut::<Quote>().unwrap();
            lhs.extend_from_slice(rhs.as_slice());

            // remove rhs from the top of the stack
            context.stack.pop();

            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn len(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Object(ref mut quote_object)] if quote_object.is::<Quote>() => {
            let quote = quote_object.downcast_ref::<Quote>().unwrap();
            let len = quote.len().try_into().map_err(|_| Symbol::RangeError)?;
            context.stack.push(Word::Integer(Integer(len)));
            Ok(())
        }
        [.., Word::Object(ref mut quote_object)] if quote_object.is::<String>() => {
            let string = quote_object.downcast_ref::<String>().unwrap();
            let len = string.len().try_into().map_err(|_| Symbol::RangeError)?;
            context.stack.push(Word::Integer(Integer(len)));
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn map(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref list_object),
            Word::Object(ref transform_object),
        ] if list_object.is::<Quote>() && transform_object.is::<Quote>() => {
            let transform_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let list_object = context.stack.pop().and_then(Word::into_object).unwrap();

            let transform = transform_object.downcast_ref::<Quote>().unwrap();
            let list = list_object.downcast_ref::<Quote>().unwrap();

            let mut accumulator = Quote::new();
            for word in list {
                context.stack.push(word.clone());
                context.unquote(transform)?;
                context
                    .stack
                    .pop()
                    .map(|w| accumulator.push(w))
                    .ok_or_else(|| {
                        context.stack.push(Word::Symbol(Symbol::LayoutError));
                        Symbol::Throw
                    })?;
            }

            context.stack.push(Word::Object(Object::new(accumulator)));
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn filter(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref list_object),
            Word::Object(ref predicate_object),
        ] if list_object.is::<Quote>() && predicate_object.is::<Quote>() => {
            let predicate_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let list_object = context.stack.pop().and_then(Word::into_object).unwrap();

            let predicate = predicate_object.downcast_ref::<Quote>().unwrap();
            let list = list_object.downcast_ref::<Quote>().unwrap();

            let mut accumulator = Quote::new();
            for word in list {
                context.stack.push(word.clone());
                context.unquote(predicate)?;

                match context.stack.pop() {
                    Some(Word::Boolean(Boolean(condition))) => {
                        if condition {
                            accumulator.push(word.clone());
                        }
                    }
                    _ => {
                        context.stack.push(Word::Symbol(Symbol::LayoutError));
                        return Err(Symbol::Throw);
                    }
                }
            }

            context.stack.push(Word::Object(Object::new(accumulator)));
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn prefix(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Object(ref quote_object)] if quote_object.is::<Quote>() => {
            let quote = quote_object.downcast_ref::<Quote>().unwrap();
            let prefix: Quote = quote
                .get(..quote.len().wrapping_sub(1))
                .unwrap_or_default()
                .iter()
                .cloned()
                .collect();

            context.stack.push(Word::Object(Object::new(prefix)));
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn suffix(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Object(ref quote_object)] if quote_object.is::<Quote>() => {
            let quote = quote_object.downcast_ref::<Quote>().unwrap();
            let suffix: Quote = quote.get(1..).unwrap_or_default().iter().cloned().collect();
            context.stack.push(Word::Object(Object::new(suffix)));
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn split(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref quote_object),
            Word::Integer(Integer(index)),
        ] if quote_object.is::<Quote>() => {
            let quote = quote_object.downcast_ref::<Quote>().unwrap();

            let index = if index >= 0 {
                usize::try_from(index).map_err(|_| Symbol::RangeError)?
            } else {
                quote.len()
                    - usize::try_from(index.unsigned_abs()).map_err(|_| Symbol::RangeError)?
            };

            let (prefix, suffix) = quote.split(index);
            let top = context.stack.len();
            context.stack[top - 1] = Word::Object(Object::new(suffix));
            context.stack[top - 2] = Word::Object(Object::new(prefix));
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn say(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Boolean(v)] => println!("{v}"),
        [.., Word::Character(v)] => println!("{v}"),
        [.., Word::Decimal(v)] => println!("{v}"),
        [.., Word::Integer(v)] => println!("{v}"),
        [.., Word::Symbol(v)] => println!("{v}"),
        [.., Word::Verb(v)] => println!("{v}"),
        [.., Word::Object(ref object)] if object.is::<String>() => {
            let string = object.downcast_ref::<String>().unwrap();
            println!("{string}")
        }
        [.., Word::Object(ref object)] if object.is::<Quote>() => {
            let quote = object.downcast_ref::<Quote>().unwrap();
            println!("{quote}")
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    context.stack.pop();
    Ok(())
}

pub fn stack_stash(context: &mut Context) -> Result<(), Symbol> {
    let stack = std::mem::take(&mut context.stack);
    let quote = Quote::from(stack);
    context.stack.push(Word::Object(Object::new(quote)));
    Ok(())
}

pub fn stack_quote(context: &mut Context) -> Result<(), Symbol> {
    let quote = Quote::from(context.stack.clone());
    context.stack.push(Word::Object(Object::new(quote)));
    Ok(())
}

pub fn stack_clear(context: &mut Context) -> Result<(), Symbol> {
    context.stack.clear();
    Ok(())
}

pub fn dup(context: &mut Context) -> Result<(), Symbol> {
    let word = context.stack.last().cloned().ok_or_else(|| {
        context.stack.push(Word::Symbol(Symbol::LayoutError));
        Symbol::Throw
    })?;

    context.stack.push(word);
    Ok(())
}

pub fn over(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., ref word, _] => {
            context.stack.push(word.clone());
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn pop(context: &mut Context) -> Result<(), Symbol> {
    context.stack.pop().map(drop).ok_or_else(|| {
        context.stack.push(Word::Symbol(Symbol::LayoutError));
        Symbol::Throw
    })
}

pub fn swap(context: &mut Context) -> Result<(), Symbol> {
    match &mut context.stack[..] {
        [.., l, r] => std::mem::swap(l, r),
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            return Err(Symbol::Throw);
        }
    }

    Ok(())
}

pub fn dip(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., _, Word::Object(ref quote_object)] if quote_object.is::<Quote>() => {
            let quote_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let backup = context.stack.pop().unwrap();

            let quote = quote_object.downcast_ref::<Quote>().unwrap();
            context.apply(quote)?;

            context.stack.push(backup);
            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn r#if(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Boolean(Boolean(condition)),
            Word::Object(ref quote_object),
        ] if quote_object.is::<Quote>() => {
            let quote_object = context.stack.pop().and_then(Word::into_object).unwrap();
            context.stack.pop();

            if condition {
                let quote = quote_object.downcast_ref::<Quote>().unwrap();
                return context.unquote(quote);
            }

            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn r#else(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Boolean(Boolean(condition)),
            Word::Object(ref quote_object),
        ] if quote_object.is::<Quote>() => {
            let quote_object = context.stack.pop().and_then(Word::into_object).unwrap();
            context.stack.pop();

            if !condition {
                let quote = quote_object.downcast_ref::<Quote>().unwrap();
                return context.unquote(quote);
            }

            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn if_else(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Boolean(Boolean(condition)),
            Word::Object(ref then_object),
            Word::Object(ref else_object),
        ] if then_object.is::<Quote>() && else_object.is::<Quote>() => {
            let r#else = context.stack.pop().and_then(Word::into_object).unwrap();
            let then = context.stack.pop().and_then(Word::into_object).unwrap();
            context.stack.pop();

            let quote_object = if condition { then } else { r#else };
            let quote = quote_object.downcast_ref::<Quote>().unwrap();

            context.unquote(quote)
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn r(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref recur_object),
            Word::Object(ref quote_object),
        ] if recur_object.is::<Quote>() && quote_object.is::<Quote>() => {
            let quote = context.stack.pop().and_then(Word::into_object).unwrap();
            let recur = context.stack.pop().and_then(Word::into_object).unwrap();

            let quote = quote.downcast_ref::<Quote>().unwrap();
            let recur = recur.downcast_ref::<Quote>().unwrap();

            context.apply_recursive(recur, quote)
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn i(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Object(ref quote_object)] if quote_object.is::<Quote>() => {
            let quote_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let quote = quote_object.downcast_ref::<Quote>().unwrap();
            context.apply(quote)
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn bi(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            ref backup,
            Word::Object(ref quote_object1),
            Word::Object(ref quote_object2),
        ] if quote_object1.is::<Quote>() && quote_object2.is::<Quote>() => {
            let backup = backup.clone();
            let quote_object2 = context.stack.pop().and_then(Word::into_object).unwrap();
            let quote_object1 = context.stack.pop().and_then(Word::into_object).unwrap();

            let quote = quote_object1.downcast_ref::<Quote>().unwrap();
            context.apply(quote)?;

            context.stack.push(backup);

            let quote = quote_object2.downcast_ref::<Quote>().unwrap();
            context.apply(quote)
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn times(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref quote_object),
            Word::Integer(Integer(n)),
        ] if quote_object.is::<Quote>() => {
            context.stack.pop();
            let quote_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let quote = quote_object.downcast_ref::<Quote>().unwrap();

            for reminder in (0..n).rev() {
                match context.unquote(quote) {
                    Ok(()) => continue,
                    Err(Symbol::Break) => {
                        context.continuation.clear();
                        return Ok(());
                    }
                    Err(Symbol::Continue) => {
                        context.continuation.clear();
                        continue;
                    }
                    effect @ Err(Symbol::Yield) => {
                        context.continuation.extend_from_slice(&[
                            Word::Object(quote_object),
                            Word::Integer(Integer(reminder)),
                            Word::Verb(Verb(times)),
                        ]);

                        return effect;
                    }
                    effect => return effect,
                }
            }

            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn r#loop(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Object(ref quote_object)] if quote_object.is::<Quote>() => {
            let quote_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let quote = quote_object.downcast_ref::<Quote>().unwrap();

            loop {
                match context.unquote(quote) {
                    Ok(()) => continue,
                    Err(Symbol::Break) => {
                        context.continuation.clear();
                        return Ok(());
                    }
                    Err(Symbol::Continue) => {
                        context.continuation.clear();
                        continue;
                    }
                    effect @ Err(Symbol::Yield) => {
                        context.continuation.extend_from_slice(&[
                            Word::Object(quote_object),
                            Word::Verb(Verb(r#loop)),
                        ]);

                        return effect;
                    }
                    effect => return effect,
                }
            }
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn perform(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [.., Word::Symbol(symbol)] => {
            context.stack.pop();
            Err(symbol)
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn install(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref quote_object),
            Word::Object(ref handle_object),
            Word::Symbol(effect),
        ] if quote_object.is::<Quote>() && handle_object.is::<Quote>() => {
            context.stack.pop();
            let handle = context.stack.pop().and_then(Word::into_object).unwrap();
            let quote = context.stack.pop().and_then(Word::into_object).unwrap();

            let quote = quote.downcast_ref::<Quote>().unwrap();
            match context.unquote(quote) {
                Err(e) if e == effect => {
                    let continuation = std::mem::take(&mut context.continuation);
                    let handle = handle.downcast_ref::<Quote>().unwrap();
                    context.stack.push(Word::Object(Object::new(continuation)));
                    context.unquote(handle)
                }
                effect => effect,
            }
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn handle(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref quote_object),
            Word::Object(ref handle_object),
        ] if quote_object.is::<Quote>() && handle_object.is::<Quote>() => {
            let handle = context.stack.pop().and_then(Word::into_object).unwrap();
            let quote = context.stack.pop().and_then(Word::into_object).unwrap();

            let quote = quote.downcast_ref::<Quote>().unwrap();
            if let Err(effect) = context.unquote(quote) {
                let continuation = std::mem::take(&mut context.continuation);
                let handle = handle.downcast_ref::<Quote>().unwrap();

                context.stack.extend_from_slice(&[
                    Word::Object(Object::new(continuation)),
                    Word::Symbol(effect),
                ]);

                return context.unquote(handle);
            }

            Ok(())
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn r#break(_: &mut Context) -> Result<(), Symbol> {
    Err(Symbol::Break)
}

pub fn r#continue(_: &mut Context) -> Result<(), Symbol> {
    Err(Symbol::Continue)
}

pub fn r#yield(_: &mut Context) -> Result<(), Symbol> {
    Err(Symbol::Yield)
}

pub fn recur(_: &mut Context) -> Result<(), Symbol> {
    Err(Symbol::Recur)
}

pub fn r#return(_: &mut Context) -> Result<(), Symbol> {
    Err(Symbol::Return)
}

pub fn r#throw(_: &mut Context) -> Result<(), Symbol> {
    Err(Symbol::Throw)
}

pub fn catch(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref try_object),
            Word::Object(ref catch_object),
        ] if try_object.is::<Quote>() && catch_object.is::<Quote>() => {
            let catch = context.stack.pop().and_then(Word::into_object).unwrap();
            let r#try = context.stack.pop().and_then(Word::into_object).unwrap();

            let r#try = r#try.downcast_ref::<Quote>().unwrap();
            match context.unquote(r#try) {
                Err(Symbol::Throw) => {
                    context.continuation.clear();
                    let catch = catch.downcast_ref::<Quote>().unwrap();
                    context.unquote(catch)
                }
                effect @ Err(Symbol::Yield) => {
                    let continuation = std::mem::take(&mut context.continuation);
                    context.continuation.extend_from_slice(&[
                        Word::Object(Object::new(continuation)),
                        Word::Object(catch),
                        Word::Verb(Verb(self::catch)),
                    ]);
                    effect
                }
                effect => effect,
            }
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn linrec(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref check_object),
            Word::Object(ref leave_object),
            Word::Object(ref shard_object),
            Word::Object(ref merge_object),
        ] if check_object.is::<Quote>()
            && leave_object.is::<Quote>()
            && shard_object.is::<Quote>()
            && merge_object.is::<Quote>() =>
        {
            let merge_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let shard_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let leave_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let check_object = context.stack.pop().and_then(Word::into_object).unwrap();

            let merge = merge_object.downcast_ref::<Quote>().unwrap();
            let shard = shard_object.downcast_ref::<Quote>().unwrap();
            let leave = leave_object.downcast_ref::<Quote>().unwrap();
            let check = check_object.downcast_ref::<Quote>().unwrap();

            linrec_aux(context, check, leave, shard, merge)
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

fn linrec_aux(
    context: &mut Context,
    check: &Quote,
    leave: &Quote,
    shard: &Quote,
    merge: &Quote,
) -> Result<(), Symbol> {
    // ---
    context.apply_sealed(check)?;
    match context.stack[..] {
        [.., Word::Boolean(Boolean(have_to_leave))] => {
            context.stack.pop();

            if have_to_leave {
                return context.apply_sealed(leave);
            }

            context.apply_sealed(shard)?;
            match context.stack[..] {
                [.., _] => {
                    linrec_aux(context, check, leave, shard, merge)?;
                    context.apply_sealed(merge)
                }
                _ => {
                    context.stack.push(Word::Symbol(Symbol::LayoutError));
                    Err(Symbol::Throw)
                }
            }
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn binrec(context: &mut Context) -> Result<(), Symbol> {
    match context.stack[..] {
        [
            ..,
            Word::Object(ref check_object),
            Word::Object(ref leave_object),
            Word::Object(ref shard_object),
            Word::Object(ref merge_object),
        ] if check_object.is::<Quote>()
            && leave_object.is::<Quote>()
            && shard_object.is::<Quote>()
            && merge_object.is::<Quote>() =>
        {
            let merge_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let shard_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let leave_object = context.stack.pop().and_then(Word::into_object).unwrap();
            let check_object = context.stack.pop().and_then(Word::into_object).unwrap();

            let merge = merge_object.downcast_ref::<Quote>().unwrap();
            let shard = shard_object.downcast_ref::<Quote>().unwrap();
            let leave = leave_object.downcast_ref::<Quote>().unwrap();
            let check = check_object.downcast_ref::<Quote>().unwrap();

            binrec_aux(context, check, leave, shard, merge)
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

fn binrec_aux(
    context: &mut Context,
    check: &Quote,
    leave: &Quote,
    shard: &Quote,
    merge: &Quote,
) -> Result<(), Symbol> {
    // ---
    context.apply_sealed(check)?;
    match context.stack[..] {
        [.., Word::Boolean(Boolean(have_to_leave))] => {
            context.stack.pop();

            if have_to_leave {
                return context.apply_sealed(leave);
            }

            context.apply_sealed(shard)?;
            match context.stack[..] {
                [.., _, _] => {
                    let backup = context.stack.pop().unwrap();
                    binrec_aux(context, check, leave, shard, merge)?;

                    context.stack.push(backup);
                    binrec_aux(context, check, leave, shard, merge)?;

                    context.apply_sealed(merge)
                }
                _ => {
                    context.stack.push(Word::Symbol(Symbol::LayoutError));
                    Err(Symbol::Throw)
                }
            }
        }
        _ => {
            context.stack.push(Word::Symbol(Symbol::LayoutError));
            Err(Symbol::Throw)
        }
    }
}

pub fn dbg(context: &mut Context) -> Result<(), Symbol> {
    let mut stdout = io::stdout().lock();

    writeln!(stdout, "K: {}", context.continuation).map_err(|_| {
        context.stack.push(Word::Symbol(Symbol::IOError));
        Symbol::Throw
    })?;

    write!(stdout, "S:").map_err(|_| {
        context.stack.push(Word::Symbol(Symbol::IOError));
        Symbol::Throw
    })?;

    context
        .stack
        .iter()
        .try_for_each(|word| write!(stdout, " {word:?}"))
        .map_err(|_| {
            context.stack.push(Word::Symbol(Symbol::IOError));
            Symbol::Throw
        })?;

    writeln!(stdout, " (top)").map_err(|_| {
        context.stack.push(Word::Symbol(Symbol::IOError));
        Symbol::Throw
    })
}

#[derive(Clone, Copy)]
enum StaticDefinition<'a> {
    Expression(&'a [Word]),
    Dictionary(&'a [(&'a Component, StaticDefinition<'a>)]),
}

impl From<StaticDefinition<'_>> for Definition {
    fn from(value: StaticDefinition) -> Self {
        match value {
            StaticDefinition::Expression(expression) => {
                Definition::new_expression(expression.into(), Visibility::Extern)
            }
            StaticDefinition::Dictionary(dictionary) => Definition::new_dictionary(
                dictionary
                    .iter()
                    .map(|(component, definition)| ((*component).into(), (*definition).into()))
                    .collect::<Dictionary>()
                    .into(),
                Visibility::Extern,
            ),
        }
    }
}

static PRELUDE: [(&Component, StaticDefinition); 75] = [
    (
        Component::try_from_literal("nan").unwrap(),
        StaticDefinition::Expression(&[Word::Decimal(Decimal::NAN)]),
    ),
    (
        Component::try_from_literal("inf").unwrap(),
        StaticDefinition::Expression(&[Word::Decimal(Decimal::INFINITY)]),
    ),
    (
        Component::try_from_literal("neg").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(neg))]),
    ),
    (
        Component::try_from_literal("incr").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(incr))]),
    ),
    (
        Component::try_from_literal("decr").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(decr))]),
    ),
    (
        Component::try_from_literal("add").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(add))]),
    ),
    (
        Component::try_from_literal("sub").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(sub))]),
    ),
    (
        Component::try_from_literal("mul").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(mul))]),
    ),
    (
        Component::try_from_literal("div").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(div))]),
    ),
    (
        Component::try_from_literal("rem").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(rem))]),
    ),
    (
        Component::try_from_literal("eq?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(is_eq))]),
    ),
    (
        Component::try_from_literal("ne?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(is_ne))]),
    ),
    (
        Component::try_from_literal("gt?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(is_gt))]),
    ),
    (
        Component::try_from_literal("ge?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(is_ge))]),
    ),
    (
        Component::try_from_literal("lt?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(is_lt))]),
    ),
    (
        Component::try_from_literal("le?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(is_le))]),
    ),
    (
        Component::try_from_literal("eq!?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(bang_is_eq))]),
    ),
    (
        Component::try_from_literal("ne!?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(bang_is_ne))]),
    ),
    (
        Component::try_from_literal("gt!?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(bang_is_gt))]),
    ),
    (
        Component::try_from_literal("ge!?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(bang_is_ge))]),
    ),
    (
        Component::try_from_literal("lt!?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(bang_is_lt))]),
    ),
    (
        Component::try_from_literal("le!?").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(bang_is_le))]),
    ),
    (
        Component::try_from_literal("true").unwrap(),
        StaticDefinition::Expression(&[Word::Boolean(Boolean(true))]),
    ),
    (
        Component::try_from_literal("false").unwrap(),
        StaticDefinition::Expression(&[Word::Boolean(Boolean(false))]),
    ),
    (
        Component::try_from_literal("not").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(not))]),
    ),
    (
        Component::try_from_literal("and").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(and))]),
    ),
    (
        Component::try_from_literal("xor").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(xor))]),
    ),
    (
        Component::try_from_literal("or").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(or))]),
    ),
    (
        Component::try_from_literal("shl").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(shl))]),
    ),
    (
        Component::try_from_literal("shr").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(shr))]),
    ),
    (
        Component::try_from_literal("ushr").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(ushr))]),
    ),
    (
        Component::try_from_literal("replace").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(replace))]),
    ),
    (
        Component::try_from_literal("set").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(set))]),
    ),
    (
        Component::try_from_literal("get").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(get))]),
    ),
    (
        Component::try_from_literal("get!").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(bang_get))]),
    ),
    (
        Component::try_from_literal("get-or-else").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(get_or_else))]),
    ),
    (
        Component::try_from_literal("shallow-bind").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(shallow_bind))]),
    ),
    (
        Component::try_from_literal("deep-bind").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(deep_bind))]),
    ),
    (
        Component::try_from_literal("quote").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(quote))]),
    ),
    (
        Component::try_from_literal("unquote").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(unquote))]),
    ),
    (
        Component::try_from_literal("cat").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(cat))]),
    ),
    (
        Component::try_from_literal("len").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(len))]),
    ),
    (
        Component::try_from_literal("map").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(map))]),
    ),
    (
        Component::try_from_literal("filter").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(filter))]),
    ),
    (
        Component::try_from_literal("prefix").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(prefix))]),
    ),
    (
        Component::try_from_literal("suffix").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(suffix))]),
    ),
    (
        Component::try_from_literal("split").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(split))]),
    ),
    (
        Component::try_from_literal("say").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(say))]),
    ),
    (
        Component::try_from_literal("stack").unwrap(),
        StaticDefinition::Dictionary(&STACK_DICTIONARY),
    ),
    (
        Component::try_from_literal("dup").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(dup))]),
    ),
    (
        Component::try_from_literal("over").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(over))]),
    ),
    (
        Component::try_from_literal("pop").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(pop))]),
    ),
    (
        Component::try_from_literal("swap").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(swap))]),
    ),
    (
        Component::try_from_literal("dip").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(dip))]),
    ),
    (
        Component::try_from_literal("if").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(r#if))]),
    ),
    (
        Component::try_from_literal("else").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(r#else))]),
    ),
    (
        Component::try_from_literal("if-else").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(if_else))]),
    ),
    (
        Component::try_from_literal("r").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(r))]),
    ),
    (
        Component::try_from_literal("i").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(i))]),
    ),
    (
        Component::try_from_literal("bi").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(bi))]),
    ),
    (
        Component::try_from_literal("times").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(times))]),
    ),
    (
        Component::try_from_literal("loop").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(r#loop))]),
    ),
    (
        Component::try_from_literal("perform").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(perform))]),
    ),
    (
        Component::try_from_literal("install").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(install))]),
    ),
    (
        Component::try_from_literal("handle").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(handle))]),
    ),
    (
        Component::try_from_literal("break").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(r#break))]),
    ),
    (
        Component::try_from_literal("continue").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(r#continue))]),
    ),
    (
        Component::try_from_literal("yield").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(r#yield))]),
    ),
    (
        Component::try_from_literal("recur").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(recur))]),
    ),
    (
        Component::try_from_literal("return").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(r#return))]),
    ),
    (
        Component::try_from_literal("throw").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(r#throw))]),
    ),
    (
        Component::try_from_literal("catch").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(catch))]),
    ),
    (
        Component::try_from_literal("linrec").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(linrec))]),
    ),
    (
        Component::try_from_literal("binrec").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(binrec))]),
    ),
    (
        Component::try_from_literal("dbg").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(dbg))]),
    ),
];

static STACK_DICTIONARY: [(&Component, StaticDefinition); 3] = [
    (
        Component::try_from_literal("stash").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(stack_stash))]),
    ),
    (
        Component::try_from_literal("quote").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(stack_quote))]),
    ),
    (
        Component::try_from_literal("clear").unwrap(),
        StaticDefinition::Expression(&[Word::Verb(Verb(stack_clear))]),
    ),
];

pub fn prelude() -> Arc<Dictionary> {
    PRELUDE
        .iter()
        .map(|(component, definition)| ((*component).into(), (*definition).into()))
        .collect::<Dictionary>()
        .into()
}
