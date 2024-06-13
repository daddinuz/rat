/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::{Debug, Display};
use std::ops::{
    Add, AddAssign, BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Div, DivAssign,
    Mul, MulAssign, Neg, Not, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign, Sub, SubAssign,
};

use crate::codegen;
use crate::decimal::Decimal;
use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;
use crate::expression::Expression;

#[derive(Default, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Integer(pub i64);

impl From<Decimal> for Integer {
    #[inline]
    fn from(value: Decimal) -> Self {
        Self::from_decimal(value)
    }
}

impl From<i64> for Integer {
    #[inline]
    fn from(value: i64) -> Self {
        Self(value)
    }
}

impl From<Integer> for i64 {
    #[inline]
    fn from(Integer(value): Integer) -> Self {
        value
    }
}

impl Integer {
    pub const BITS: u32 = i64::BITS;
    pub const ZERO: Self = Self(0);

    #[inline]
    pub const fn from_decimal(Decimal(value): Decimal) -> Self {
        Self(value as _)
    }

    #[inline]
    pub const fn as_decimal(self) -> Decimal {
        Decimal::from_integer(self)
    }

    #[inline]
    pub const fn ushr(self, Self(value): Self) -> Self {
        Self((self.0 as u64 >> value) as _)
    }

    #[inline]
    pub const fn is_positive(self) -> bool {
        self.0.is_positive()
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        self.0 == 0
    }

    #[inline]
    pub const fn is_negative(self) -> bool {
        self.0.is_negative()
    }
}

impl Evaluate<&mut Evaluator> for Integer {
    type Output = Result<(), Effect>;

    fn evaluate(self, evaluator: &mut Evaluator) -> Self::Output {
        evaluator.stack.push(Expression::Integer(self));
        Ok(())
    }
}

codegen::unary_operator!(Integer, Neg::neg, Not::not);

codegen::binary_operator!(
    Integer,
    Add::add,
    Sub::sub,
    Mul::mul,
    Div::div,
    Rem::rem,
    BitAnd::bitand,
    BitXor::bitxor,
    BitOr::bitor,
    Shl::shl,
    Shr::shr,
);

codegen::binary_assign_operator!(
    Integer,
    AddAssign::add_assign,
    SubAssign::sub_assign,
    MulAssign::mul_assign,
    DivAssign::div_assign,
    RemAssign::rem_assign,
    BitAndAssign::bitand_assign,
    BitXorAssign::bitxor_assign,
    BitOrAssign::bitor_assign,
    ShlAssign::shl_assign,
    ShrAssign::shr_assign,
);

impl Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Debug for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.0)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn from_decimal() {
        let decimal = Decimal(3.14);
        let value: Integer = Integer::from_decimal(decimal);
        assert_eq!(value, decimal.into());
        assert_eq!(value, Integer(3));
    }

    #[test]
    fn from_integer() {
        assert_eq!(Integer::from(42), Integer(42));
    }

    #[test]
    fn as_integer() {
        let value = Decimal(42.0);
        assert_eq!(value.as_integer(), Integer(42));
    }

    #[test]
    fn bits() {
        assert_eq!(Integer::BITS, i64::BITS);
    }

    #[test]
    fn zero() {
        assert_eq!(Integer::ZERO, Integer(0));
    }

    #[test]
    fn neg() {
        let value: Integer = -Integer(10);
        assert_eq!(value, Integer(-10));
    }

    #[test]
    fn add() {
        let value: Integer = Integer(5) + Integer(3);
        assert_eq!(value, Integer(8));
    }

    #[test]
    fn sub() {
        let value: Integer = Integer(10) - Integer(3);
        assert_eq!(value, Integer(7));
    }

    #[test]
    fn mul() {
        let value: Integer = Integer(4) * Integer(5);
        assert_eq!(value, Integer(20));
    }

    #[test]
    fn div() {
        let value: Integer = Integer(10) / Integer(2);
        assert_eq!(value, Integer(5));
    }

    #[test]
    fn rem() {
        let value: Integer = Integer(10) % Integer(3);
        assert_eq!(value, Integer(1));
    }

    #[test]
    fn shl() {
        let value: Integer = Integer(5) << Integer(2);
        assert_eq!(value, Integer(20));
    }

    #[test]
    fn shr() {
        let value: Integer = Integer(20) >> Integer(2);
        assert_eq!(value, Integer(5));

        let value: Integer = Integer(-1) >> Integer((Integer::BITS - 1) as _);
        assert_eq!(value, Integer(-1));
    }

    #[test]
    fn ushr() {
        let value: Integer = Integer(100).ushr(Integer(2));
        assert_eq!(value, Integer(25));

        let value: Integer = Integer(-1).ushr(Integer((Integer::BITS - 1) as _));
        assert_eq!(value, Integer(1));
    }

    #[test]
    fn eq() {
        let value1: Integer = Integer(10);
        let value2: Integer = Integer(10);
        assert_eq!(value1, value2);
    }

    #[test]
    fn ne() {
        let value1: Integer = Integer(10);
        let value2: Integer = Integer(20);
        assert_ne!(value1, value2);
    }

    #[test]
    fn lt() {
        let value1: Integer = Integer(10);
        let value2: Integer = Integer(20);
        assert!(value1 < value2);
    }

    #[test]
    fn le() {
        let value1: Integer = Integer(10);
        let value2: Integer = Integer(20);
        let value3: Integer = Integer(10);
        assert!(value1 <= value2);
        assert!(value1 <= value3);
    }

    #[test]
    fn gt() {
        let value1: Integer = Integer(20);
        let value2: Integer = Integer(10);
        assert!(value1 > value2);
    }

    #[test]
    fn ge() {
        let value1: Integer = Integer(20);
        let value2: Integer = Integer(10);
        let value3: Integer = Integer(20);
        assert!(value1 >= value2);
        assert!(value1 >= value3);
    }

    #[test]
    fn display() {
        let value: Integer = Integer(42);
        assert_eq!(format!("{}", value), "42");
    }

    #[test]
    fn debug() {
        let value: Integer = Integer(42);
        assert_eq!(format!("{:?}", value), "42");
    }
}
