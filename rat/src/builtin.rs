/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::io::{self, Write};

use crate::error::RuntimeError;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;

use crate::expression::Expression;

use crate::boolean::Boolean;
use crate::decimal::Decimal;
use crate::integer::Integer;
use crate::quote::Quote;
use crate::string::String;
use crate::symbol::Symbol;

pub fn neg(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., Expression::Integer(lhs)] => {
            *lhs = -*lhs;
            Ok(())
        }
        [.., Expression::Decimal(lhs)] => {
            *lhs = -*lhs;
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn incr(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., Expression::Integer(lhs)] => {
            *lhs += Integer(1);
            Ok(())
        }
        [.., Expression::Decimal(lhs)] => {
            *lhs += Decimal(1.0);
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn decr(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., Expression::Integer(lhs)] => {
            *lhs -= Integer(1);
            Ok(())
        }
        [.., Expression::Decimal(lhs)] => {
            *lhs -= Decimal(1.0);
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn add(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs += rhs;
            stack.pop();
            Ok(())
        }
        [.., Expression::Decimal(ref mut lhs), Expression::Decimal(rhs)] => {
            *lhs += rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn sub(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs -= rhs;
            stack.pop();
            Ok(())
        }
        [.., Expression::Decimal(ref mut lhs), Expression::Decimal(rhs)] => {
            *lhs -= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn mul(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs *= rhs;
            stack.pop();
            Ok(())
        }
        [.., Expression::Decimal(ref mut lhs), Expression::Decimal(rhs)] => {
            *lhs *= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn div(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(_), Expression::Integer(Integer::ZERO)] => {
            stack.push(Symbol::divide_by_zero().into());
            Err(RuntimeError)
        }
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs /= rhs;
            stack.pop();
            Ok(())
        }
        [.., Expression::Decimal(ref mut lhs), Expression::Decimal(rhs)] => {
            *lhs /= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn rem(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(_), Expression::Integer(Integer::ZERO)] => {
            stack.push(Symbol::divide_by_zero().into());
            Err(RuntimeError)
        }
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs %= rhs;
            stack.pop();
            Ok(())
        }
        [.., Expression::Decimal(ref mut lhs), Expression::Decimal(rhs)] => {
            *lhs %= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn eq(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., ref mut lhs, ref rhs] => {
            *lhs = Expression::Boolean(Boolean(*lhs == *rhs));
            stack.pop();
            Ok(())
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn ne(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., ref mut lhs, ref rhs] => {
            *lhs = Expression::Boolean(Boolean(*lhs != *rhs));
            stack.pop();
            Ok(())
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn gt(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., ref mut lhs @ Expression::Integer(_), Expression::Integer(r)] => match *lhs {
            Expression::Integer(l) => {
                *lhs = Expression::Boolean(Boolean(l > r));
                stack.pop();
                Ok(())
            }
            _ => unreachable!(),
        },
        [.., ref mut lhs @ Expression::Decimal(_), Expression::Decimal(r)] => match *lhs {
            Expression::Decimal(l) => {
                *lhs = Expression::Boolean(Boolean(l > r));
                stack.pop();
                Ok(())
            }
            _ => unreachable!(),
        },
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn ge(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., ref mut lhs @ Expression::Integer(_), Expression::Integer(r)] => match *lhs {
            Expression::Integer(l) => {
                *lhs = Expression::Boolean(Boolean(l >= r));
                stack.pop();
                Ok(())
            }
            _ => unreachable!(),
        },
        [.., ref mut lhs @ Expression::Decimal(_), Expression::Decimal(r)] => match *lhs {
            Expression::Decimal(l) => {
                *lhs = Expression::Boolean(Boolean(l >= r));
                stack.pop();
                Ok(())
            }
            _ => unreachable!(),
        },
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn lt(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., ref mut lhs @ Expression::Integer(_), Expression::Integer(r)] => match *lhs {
            Expression::Integer(l) => {
                *lhs = Expression::Boolean(Boolean(l < r));
                stack.pop();
                Ok(())
            }
            _ => unreachable!(),
        },
        [.., ref mut lhs @ Expression::Decimal(_), Expression::Decimal(r)] => match *lhs {
            Expression::Decimal(l) => {
                *lhs = Expression::Boolean(Boolean(l < r));
                stack.pop();
                Ok(())
            }
            _ => unreachable!(),
        },
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn le(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., ref mut lhs @ Expression::Integer(_), Expression::Integer(r)] => match *lhs {
            Expression::Integer(l) => {
                *lhs = Expression::Boolean(Boolean(l <= r));
                stack.pop();
                Ok(())
            }
            _ => unreachable!(),
        },
        [.., ref mut lhs @ Expression::Decimal(_), Expression::Decimal(r)] => match *lhs {
            Expression::Decimal(l) => {
                *lhs = Expression::Boolean(Boolean(l <= r));
                stack.pop();
                Ok(())
            }
            _ => unreachable!(),
        },
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn positive(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::Integer(n)] => {
            *stack.last_mut().unwrap() = Expression::Boolean(Boolean(n.is_positive()));
            Ok(())
        }
        [.., Expression::Decimal(n)] => {
            *stack.last_mut().unwrap() = Expression::Boolean(Boolean(n.is_positive()));
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn zero(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::Integer(n)] => {
            *stack.last_mut().unwrap() = Expression::Boolean(Boolean(n.is_zero()));
            Ok(())
        }
        [.., Expression::Decimal(n)] => {
            *stack.last_mut().unwrap() = Expression::Boolean(Boolean(n.is_zero()));
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn negative(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::Integer(n)] => {
            *stack.last_mut().unwrap() = Expression::Boolean(Boolean(n.is_negative()));
            Ok(())
        }
        [.., Expression::Decimal(n)] => {
            *stack.last_mut().unwrap() = Expression::Boolean(Boolean(n.is_negative()));
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn not(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., Expression::Boolean(lhs)] => {
            *lhs = !*lhs;
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn and(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Boolean(ref mut lhs), Expression::Boolean(rhs)] => {
            *lhs &= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn or(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Boolean(ref mut lhs), Expression::Boolean(rhs)] => {
            *lhs |= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn bitwise_not(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., Expression::Integer(lhs)] => {
            *lhs = !*lhs;
            Ok(())
        }
        [.., Expression::Boolean(lhs)] => {
            *lhs = !*lhs;
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn bitwise_and(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs &= rhs;
            stack.pop();
            Ok(())
        }
        [.., Expression::Boolean(ref mut lhs), Expression::Boolean(rhs)] => {
            *lhs &= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn bitwise_xor(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs ^= rhs;
            stack.pop();
            Ok(())
        }
        [.., Expression::Boolean(ref mut lhs), Expression::Boolean(rhs)] => {
            *lhs ^= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn bitwise_or(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs |= rhs;
            stack.pop();
            Ok(())
        }
        [.., Expression::Boolean(ref mut lhs), Expression::Boolean(rhs)] => {
            *lhs |= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn shl(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs <<= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn shr(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs >>= rhs;
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn ushr(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Integer(ref mut lhs), Expression::Integer(rhs)] => {
            *lhs = lhs.ushr(rhs);
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn cat(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., Expression::Quote(lhs), Expression::Quote(rhs)] => {
            let rhs = std::mem::take(rhs);
            lhs.extend(rhs);
            stack.pop();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn quote(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;
    let expression = stack.pop().ok_or_else(|| {
        stack.push(Symbol::stack_underflow().into());
        RuntimeError
    })?;

    stack.push(Expression::Quote(Quote::from([expression])));
    Ok(())
}

pub fn unquote(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    match evaluator.stack.pop() {
        Some(Expression::Quote(quote)) => evaluator.evaluate(quote.iter().cloned()),
        Some(expression) => {
            evaluator
                .stack
                .extend_from_slice(&[expression, Symbol::type_error().into()]);
            Err(RuntimeError)
        }
        _ => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn eval(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack.pop() {
        Some(expression) => evaluator.evaluate(expression),
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn i(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::Quote(_)] => unquote(evaluator),
        [.., _] => eval(evaluator),
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn x(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;
    let expression = stack.last().cloned().ok_or_else(|| {
        stack.push(Symbol::stack_underflow().into());
        RuntimeError
    })?;

    stack.push(expression);
    i(evaluator)
}

pub fn unary2(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;
    let top = stack.len();

    match stack[..] {
        [.., _, ref mut input2, Expression::Quote(ref mut quote)] => {
            let quote = std::mem::take(quote);
            let input2 = std::mem::replace(input2, Expression::Integer(Integer::ZERO));

            stack.truncate(top - 2);
            evaluator.evaluate(quote.iter().cloned())?;

            evaluator.stack.push(input2);
            evaluator.evaluate(quote.iter().cloned())
        }
        [.., _, _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn dip(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    match &evaluator.stack[..] {
        [.., _, Expression::Quote(_)] => {
            let top = evaluator.stack.len();
            let expression = evaluator.stack.swap_remove(top - 2);
            i(evaluator)?;
            evaluator.stack.push(expression);
            Ok(())
        }
        [.., _, _] => {
            evaluator.stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn r#if(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Boolean(Boolean(condition)), Expression::Quote(ref mut truthy)] => {
            if condition {
                let quote = std::mem::take(truthy);
                let top = stack.len();
                stack.truncate(top - 2);
                return evaluator.evaluate(quote.iter().cloned());
            }

            let top = stack.len();
            stack.truncate(top - 2);
            Ok(())
        }
        [.., _, _, _] => {
            evaluator.stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn r#else(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Boolean(Boolean(condition)), Expression::Quote(ref mut falsy)] => {
            if !condition {
                let quote = std::mem::take(falsy);
                let top = stack.len();
                stack.truncate(top - 2);
                return evaluator.evaluate(quote.iter().cloned());
            }

            let top = stack.len();
            stack.truncate(top - 2);
            Ok(())
        }
        [.., _, _] => {
            evaluator.stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn if_else(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Boolean(Boolean(condition)), Expression::Quote(ref mut truthy), Expression::Quote(ref mut falsy)] =>
        {
            let quote = std::mem::take(if condition { truthy } else { falsy });
            let top = stack.len();
            stack.truncate(top - 3);
            evaluator.evaluate(quote.iter().cloned())
        }
        [.., _, _, _] => {
            evaluator.stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn raise(_: &mut Evaluator) -> Result<(), RuntimeError> {
    Err(RuntimeError)
}

pub fn r#try(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    match &evaluator.stack[..] {
        [.., Expression::Quote(_), Expression::Quote(_), _] => {
            let guarded = evaluator.stack.pop();
            let guard = evaluator.stack.pop().unwrap();
            let len = evaluator.stack.len();

            match unquote(evaluator) {
                Err(RuntimeError) if evaluator.stack.last() == guarded.as_ref() => {
                    evaluator.stack.truncate(len);
                    evaluator.stack[len - 1] = guard;
                    unquote(evaluator)
                }
                flow => flow,
            }
        }
        [.., _, _, _] => {
            evaluator.stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn first(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::Quote(quote)] => {
            let expression = quote.first().cloned().ok_or_else(|| {
                stack.push(Symbol::out_of_range().into());
                RuntimeError
            })?;
            *stack.last_mut().unwrap() = expression;
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn last(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::Quote(quote)] => {
            let expression = quote.last().cloned().ok_or_else(|| {
                stack.push(Symbol::out_of_range().into());
                RuntimeError
            })?;
            *stack.last_mut().unwrap() = expression;
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn prefix(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::Quote(quote)] => {
            let quote_len = quote.len();
            *stack.last_mut().unwrap() = Expression::Quote(
                quote
                    .get(..quote_len - 1)
                    .unwrap_or_default()
                    .iter()
                    .cloned()
                    .collect(),
            );

            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn suffix(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::Quote(quote)] => {
            *stack.last_mut().unwrap() =
                Expression::Quote(quote.get(1..).unwrap_or_default().iter().cloned().collect());
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn at(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Quote(ref quote), Expression::Integer(Integer(at))] => {
            let quote_len = quote.len();

            if at.is_negative() || (at as usize) >= quote_len {
                stack.push(Symbol::out_of_range().into());
                return Err(RuntimeError);
            }

            let expression = quote[at as usize].clone();

            stack.pop();
            *stack.last_mut().unwrap() = expression;
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn split(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match stack[..] {
        [.., Expression::Quote(ref mut quote), Expression::Integer(Integer(at))] => {
            let quote_len = quote.len();

            if at.is_negative() || (at as usize) >= quote_len {
                stack.push(Symbol::out_of_range().into());
                return Err(RuntimeError);
            }

            *stack.last_mut().unwrap() = quote.split(at as usize).into();
            Ok(())
        }
        [.., _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn len(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::Quote(quote)] => {
            *stack.last_mut().unwrap() = Expression::Integer(Integer(quote.len() as _));
            Ok(())
        }
        [.., Expression::String(string)] => {
            *stack.last_mut().unwrap() = Expression::Integer(Integer(string.len() as _));
            Ok(())
        }
        [.., _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn swap(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;
    let top = stack.len();

    if top < 2 {
        stack.push(Symbol::stack_underflow().into());
        return Err(RuntimeError);
    }

    stack.swap(top - 1, top - 2);
    Ok(())
}

pub fn rollup(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., x, y, z] => {
            std::mem::swap(y, z);
            std::mem::swap(x, y);
            Ok(())
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn rolldown(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., x, y, z] => {
            std::mem::swap(x, y);
            std::mem::swap(y, z);
            Ok(())
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn rotate(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., x, _, z] => {
            std::mem::swap(x, z);
            Ok(())
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn pop(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    if stack.pop().is_none() {
        stack.push(Symbol::stack_underflow().into());
        return Err(RuntimeError);
    }

    Ok(())
}

pub fn dup(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;
    let expression = stack.last().cloned().ok_or_else(|| {
        stack.push(Symbol::stack_underflow().into());
        RuntimeError
    })?;

    stack.push(expression);
    Ok(())
}

pub fn ask(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &stack[..] {
        [.., Expression::String(prompt)] => {
            let mut stdout_lock = io::stdout().lock();

            write!(stdout_lock, "{prompt}").map_err(|_| {
                stack.push(Symbol::io_error().into());
                RuntimeError
            })?;

            stdout_lock.flush().map_err(|_| {
                stack.push(Symbol::io_error().into());
                RuntimeError
            })?;

            stack.pop();
        }
        [.., _] => {
            evaluator.stack.push(Symbol::type_error().into());
            return Err(RuntimeError);
        }
        _ => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            return Err(RuntimeError);
        }
    }

    let mut buf = std::string::String::new();

    io::stdin().read_line(&mut buf).map_err(|_| {
        stack.push(Symbol::io_error().into());
        RuntimeError
    })?;

    stack.push(Expression::String(String::from_utf8(&buf)));
    Ok(())
}

pub fn say(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    let expression = stack.pop().ok_or_else(|| {
        stack.push(Symbol::stack_underflow().into());
        RuntimeError
    })?;

    writeln!(io::stdout(), "{expression}").map_err(|_| {
        stack.push(Symbol::io_error().into());
        RuntimeError
    })
}

pub fn show(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;
    let mut stdout = io::stdout().lock();

    write!(stdout, "#>>>").map_err(|_| {
        stack.push(Symbol::io_error().into());
        RuntimeError
    })?;

    stack
        .iter()
        .try_for_each(|e| write!(stdout, " {e:?}"))
        .map_err(|_| {
            stack.push(Symbol::io_error().into());
            RuntimeError
        })?;

    writeln!(stdout).map_err(|_| {
        stack.push(Symbol::io_error().into());
        RuntimeError
    })
}

pub fn linrec(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., Expression::Quote(check), Expression::Quote(leave), Expression::Quote(shard), Expression::Quote(merge)] =>
        {
            let merge = std::mem::take(merge);
            let shard = std::mem::take(shard);
            let leave = std::mem::take(leave);
            let check = std::mem::take(check);

            let top = stack.len();
            stack.truncate(top - 4);

            linrec_aux(evaluator, &check, &leave, &shard, &merge)
        }
        [.., _, _, _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

fn linrec_aux(
    evaluator: &mut Evaluator,
    check: &Quote,
    leave: &Quote,
    shard: &Quote,
    merge: &Quote,
) -> Result<(), RuntimeError> {
    evaluator.evaluate(check.iter().cloned())?;

    match evaluator.stack.pop() {
        Some(Expression::Boolean(Boolean(false))) => {
            evaluator.evaluate(shard.iter().cloned())?;
            linrec_aux(evaluator, check, leave, shard, merge)?;
            evaluator.evaluate(merge.iter().cloned())
        }
        Some(Expression::Boolean(Boolean(true))) => evaluator.evaluate(leave.iter().cloned()),
        Some(expression) => {
            evaluator
                .stack
                .extend_from_slice(&[expression, Symbol::type_error().into()]);

            Err(RuntimeError)
        }
        None => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn binrec(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    let stack = &mut evaluator.stack;

    match &mut stack[..] {
        [.., Expression::Quote(check), Expression::Quote(leave), Expression::Quote(shard), Expression::Quote(merge)] =>
        {
            let merge = std::mem::take(merge);
            let shard = std::mem::take(shard);
            let leave = std::mem::take(leave);
            let check = std::mem::take(check);

            let top = stack.len();
            stack.truncate(top - 4);

            binrec_aux(evaluator, &check, &leave, &shard, &merge)
        }
        [.., _, _, _, _] => {
            stack.push(Symbol::type_error().into());
            Err(RuntimeError)
        }
        _ => {
            stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

fn binrec_aux(
    evaluator: &mut Evaluator,
    check: &Quote,
    leave: &Quote,
    shard: &Quote,
    merge: &Quote,
) -> Result<(), RuntimeError> {
    evaluator.evaluate(check.iter().cloned())?;

    match evaluator.stack.pop() {
        Some(Expression::Boolean(Boolean(false))) => {
            evaluator.evaluate(shard.iter().cloned())?;

            let expression = evaluator.stack.pop().unwrap();
            binrec_aux(evaluator, check, leave, shard, merge)?;

            evaluator.stack.push(expression);
            binrec_aux(evaluator, check, leave, shard, merge)?;

            evaluator.evaluate(merge.iter().cloned())
        }
        Some(Expression::Boolean(Boolean(true))) => evaluator.evaluate(leave.iter().cloned()),
        Some(expression) => {
            evaluator
                .stack
                .extend_from_slice(&[expression, Symbol::type_error().into()]);

            Err(RuntimeError)
        }
        None => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}

pub fn bind(evaluator: &mut Evaluator) -> Result<(), RuntimeError> {
    match evaluator.stack.pop() {
        Some(Expression::Quote(quote)) => {
            let mut top = evaluator.stack.len();
            let expression = quote
                .iter()
                .rev()
                .map(|e| match e {
                    Expression::Symbol(_) => {
                        top -= 1;
                        evaluator.stack.get(top).cloned().ok_or(RuntimeError)
                    }
                    _ => Ok(e.clone()),
                })
                .collect::<Result<Vec<_>, _>>()
                .map(|mut q| {
                    q.reverse();
                    Expression::Quote(Quote::from(q))
                })
                .inspect_err(|_| {
                    evaluator.stack.extend_from_slice(&[
                        Expression::Quote(quote),
                        Symbol::stack_underflow().into(),
                    ]);
                })?;

            evaluator.stack.truncate(top);
            evaluator.stack.push(expression);
            Ok(())
        }
        Some(expression) => {
            evaluator
                .stack
                .extend_from_slice(&[expression, Symbol::type_error().into()]);

            Err(RuntimeError)
        }
        None => {
            evaluator.stack.push(Symbol::stack_underflow().into());
            Err(RuntimeError)
        }
    }
}
