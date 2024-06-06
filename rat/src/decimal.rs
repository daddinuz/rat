/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::cmp::Ordering;
use std::fmt::{Debug, Display};
use std::hash::{Hash, Hasher};
use std::num::FpCategory;
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

use crate::codegen;
use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;
use crate::expression::Expression;
use crate::integer::Integer;

#[derive(Default, Copy, Clone)]
pub struct Decimal(pub f64);

impl From<Integer> for Decimal {
    #[inline]
    fn from(value: Integer) -> Self {
        Self::from_integer(value)
    }
}

impl From<f64> for Decimal {
    #[inline]
    fn from(value: f64) -> Self {
        Self(value)
    }
}

impl From<Decimal> for f64 {
    #[inline]
    fn from(Decimal(value): Decimal) -> Self {
        value
    }
}

impl Decimal {
    pub const NAN: Self = Self(f64::NAN);
    pub const ZERO: Self = Self(0.0);
    pub const NEG_ZERO: Self = Self(-0.0);
    pub const INFINITY: Self = Self(f64::INFINITY);
    pub const NEG_INFINITY: Self = Self(f64::NEG_INFINITY);

    #[inline]
    pub const fn from_integer(Integer(value): Integer) -> Self {
        Self(value as _)
    }

    #[inline]
    pub const fn as_integer(self) -> Integer {
        Integer::from_decimal(self)
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        matches!(self.0.classify(), FpCategory::Zero)
    }
}

impl Evaluate<&mut Evaluator> for Decimal {
    type Output = Result<(), Effect>;

    fn evaluate(self, evaluator: &mut Evaluator) -> Self::Output {
        evaluator.stack.push(Expression::Decimal(self));
        Ok(())
    }
}

codegen::unary_operator!(Decimal, Neg::neg);

codegen::binary_operator!(Decimal, Add::add, Sub::sub, Mul::mul, Div::div, Rem::rem);

codegen::binary_assign_operator!(
    Decimal,
    AddAssign::add_assign,
    SubAssign::sub_assign,
    MulAssign::mul_assign,
    DivAssign::div_assign,
    RemAssign::rem_assign
);

impl PartialEq for Decimal {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0).is_eq()
    }
}

impl Eq for Decimal {}

impl PartialOrd for Decimal {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Decimal {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.total_cmp(&other.0)
    }
}

impl Hash for Decimal {
    // see documentation of `total_cmp` at https://doc.rust-lang.org/nightly/src/core/num/f64.rs.html#1372
    fn hash<H: Hasher>(&self, state: &mut H) {
        const BITS_MINUS_ONE: u32 = i64::BITS - 1;
        let mut bits = self.0.to_bits() as i64;
        bits ^= (((bits >> BITS_MINUS_ONE) as u64) >> 1) as i64;
        bits.hash(state);
    }
}

impl Display for Decimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Debug for Decimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.0.classify() {
            FpCategory::Nan => write!(f, "0.NaN"),
            FpCategory::Infinite => write!(
                f,
                "{}",
                if self.0.is_sign_positive() {
                    "+∞"
                } else {
                    "-∞"
                }
            ),
            _ => write!(f, "{:?}", self.0),
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn from_integer() {
        let integer = Integer(42);
        let value: Decimal = Decimal::from_integer(integer);
        assert_eq!(value, integer.into());
        assert_eq!(value, Decimal(42.0));
    }

    #[test]
    fn from_decimal() {
        assert_eq!(Decimal::from(3.14), Decimal(3.14));
    }

    #[test]
    fn as_decimal() {
        let value: Integer = Integer(42);
        assert_eq!(value.as_decimal(), Decimal(42.0));
    }

    #[test]
    fn zero() {
        assert_eq!(Decimal::ZERO, Decimal(0.0));
        assert_eq!(Decimal::NEG_ZERO, Decimal(-0.0));
    }

    #[test]
    fn neg() {
        let value: Decimal = -Decimal(2.5);
        assert_eq!(value, Decimal(-2.5));
    }

    #[test]
    fn add() {
        let value: Decimal = Decimal(2.5) + Decimal(3.5);
        assert_eq!(value, Decimal(6.0));
    }

    #[test]
    fn sub() {
        let value: Decimal = Decimal(5.0) - Decimal(2.5);
        assert_eq!(value, Decimal(2.5));
    }

    #[test]
    fn mul() {
        let value: Decimal = Decimal(2.5) * Decimal(3.0);
        assert_eq!(value, Decimal(7.5));
    }

    #[test]
    fn div() {
        let value: Decimal = Decimal(5.0) / Decimal(2.0);
        assert_eq!(value, Decimal(2.5));
    }

    #[test]
    fn rem() {
        let value: Decimal = Decimal(5.5) % Decimal(2.0);
        assert_eq!(value, Decimal(1.5));
    }

    #[test]
    fn eq() {
        let value1: Decimal = Decimal(10.0);
        let value2: Decimal = Decimal(10.0);
        assert_eq!(value1, value2);
    }

    #[test]
    fn ne() {
        let value1: Decimal = Decimal(10.0);
        let value2: Decimal = Decimal(20.0);
        assert_ne!(value1, value2);
    }

    #[test]
    fn lt() {
        let value1: Decimal = Decimal(10.0);
        let value2: Decimal = Decimal(20.0);
        assert!(value1 < value2);
    }

    #[test]
    fn le() {
        let value1: Decimal = Decimal(10.0);
        let value2: Decimal = Decimal(20.0);
        let value3: Decimal = Decimal(10.0);
        assert!(value1 <= value2);
        assert!(value1 <= value3);
    }

    #[test]
    fn gt() {
        let value1: Decimal = Decimal(20.0);
        let value2: Decimal = Decimal(10.0);
        assert!(value1 > value2);
    }

    #[test]
    fn ge() {
        let value1: Decimal = Decimal(20.0);
        let value2: Decimal = Decimal(10.0);
        let value3: Decimal = Decimal(20.0);
        assert!(value1 >= value2);
        assert!(value1 >= value3);
    }

    #[test]
    fn display() {
        let value: Decimal = Decimal(3.14);
        assert_eq!(format!("{}", value), "3.14");

        let value: Decimal = Decimal(0.0);
        assert_eq!(format!("{}", value), "0.0");
    }

    #[test]
    fn debug() {
        let value: Decimal = Decimal(3.14);
        assert_eq!(format!("{:?}", value), "3.14");

        let value: Decimal = Decimal(0.0);
        assert_eq!(format!("{:?}", value), "0.0");
    }
}
