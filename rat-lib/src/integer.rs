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

#[derive(Clone, Copy, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(transparent)]
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
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    #[inline]
    pub const fn from_decimal(Decimal(value): Decimal) -> Self {
        Self(value as _)
    }

    #[inline]
    pub const fn to_decimal(self) -> Decimal {
        Decimal::from_integer(self)
    }

    #[inline]
    pub const fn ushr(self, Self(rhs): Self) -> Self {
        let Self(lhs) = self;
        Self((lhs as u64 >> rhs) as _)
    }

    #[inline]
    pub const fn is_positive(self) -> bool {
        let Self(value) = self;
        value.is_positive()
    }

    #[inline]
    pub const fn is_zero(self) -> bool {
        let Self(value) = self;
        value == 0
    }

    #[inline]
    pub const fn is_negative(self) -> bool {
        let Self(value) = self;
        value.is_negative()
    }
}

impl Display for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Debug for Integer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(value) = self;
        write!(f, "{value:?}")
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn from_decimal() {
        let decimal = Decimal(3.14);
        let sut = Integer::from_decimal(decimal);
        assert_eq!(sut, decimal.into());
        assert_eq!(sut, Integer(3));
    }

    #[test]
    fn from_integer() {
        assert_eq!(Integer::from(42), Integer(42));
    }

    #[test]
    fn to_integer() {
        let sut = Decimal(42.0);
        assert_eq!(sut.to_integer(), Integer(42));
    }

    #[test]
    fn zero() {
        assert_eq!(Integer::ZERO, Integer(0));
    }

    #[test]
    fn neg() {
        let sut = -Integer(10);
        assert_eq!(sut, Integer(-10));
    }

    #[test]
    fn add() {
        let sut = Integer(5) + Integer(3);
        assert_eq!(sut, Integer(8));
    }

    #[test]
    fn sub() {
        let sut = Integer(10) - Integer(3);
        assert_eq!(sut, Integer(7));
    }

    #[test]
    fn mul() {
        let sut = Integer(4) * Integer(5);
        assert_eq!(sut, Integer(20));
    }

    #[test]
    fn div() {
        let sut = Integer(10) / Integer(2);
        assert_eq!(sut, Integer(5));
    }

    #[test]
    fn rem() {
        let sut = Integer(10) % Integer(3);
        assert_eq!(sut, Integer(1));
    }

    #[test]
    fn shl() {
        let sut = Integer(5) << Integer(2);
        assert_eq!(sut, Integer(20));
    }

    #[test]
    fn shr() {
        let sut = Integer(20) >> Integer(2);
        assert_eq!(sut, Integer(5));

        let sut = Integer(-1) >> Integer(63);
        assert_eq!(sut, Integer(-1));
    }

    #[test]
    fn ushr() {
        let sut = Integer(100).ushr(Integer(2));
        assert_eq!(sut, Integer(25));

        let sut = Integer(-1).ushr(Integer(63));
        assert_eq!(sut, Integer(1));
    }

    #[test]
    fn eq() {
        let sut1 = Integer(10);
        let sut2 = Integer(10);
        assert_eq!(sut1, sut2);
    }

    #[test]
    fn ne() {
        let sut1 = Integer(10);
        let sut2 = Integer(20);
        assert_ne!(sut1, sut2);
    }

    #[test]
    fn lt() {
        let sut1 = Integer(10);
        let sut2 = Integer(20);
        assert!(sut1 < sut2);
    }

    #[test]
    fn le() {
        let sut1 = Integer(10);
        let sut2 = Integer(20);
        let sut3 = Integer(10);
        assert!(sut1 <= sut2);
        assert!(sut1 <= sut3);
    }

    #[test]
    fn gt() {
        let sut1 = Integer(20);
        let sut2 = Integer(10);
        assert!(sut1 > sut2);
    }

    #[test]
    fn ge() {
        let sut1 = Integer(20);
        let sut2 = Integer(10);
        let sut3 = Integer(20);
        assert!(sut1 >= sut2);
        assert!(sut1 >= sut3);
    }

    #[test]
    fn display() {
        let sut = Integer(42);
        assert_eq!(format!("{}", sut), "42");
    }

    #[test]
    fn debug() {
        let sut = Integer(42);
        assert_eq!(format!("{:?}", sut), "42");
    }
}
