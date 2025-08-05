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
use crate::integer::Integer;

#[derive(Clone, Copy, Default)]
#[repr(transparent)]
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
    pub const ZERO: Self = Self(0.0);
    pub const ONE: Self = Self(1.0);
    pub const NAN: Self = Self(f64::NAN);
    pub const INFINITY: Self = Self(f64::INFINITY);

    #[inline]
    pub const fn from_integer(Integer(value): Integer) -> Self {
        Self(value as _)
    }

    #[inline]
    pub const fn to_integer(self) -> Integer {
        Integer::from_decimal(self)
    }

    #[inline]
    pub fn is_positive(self) -> bool {
        let Self(value) = self;
        value.is_sign_positive()
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        let Self(value) = self;
        matches!(value.classify(), FpCategory::Zero)
    }

    #[inline]
    pub fn is_negative(self) -> bool {
        let Self(value) = self;
        value.is_sign_negative()
    }
}

impl PartialEq for Decimal {
    #[inline]
    fn eq(&self, Self(rhs): &Self) -> bool {
        let Self(lhs) = self;
        lhs.total_cmp(rhs).is_eq()
    }
}

impl Eq for Decimal {}

impl PartialOrd for Decimal {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Decimal {
    #[inline]
    fn cmp(&self, Self(rhs): &Self) -> Ordering {
        let Self(lhs) = self;
        lhs.total_cmp(rhs)
    }
}

impl Hash for Decimal {
    // see documentation of `total_cmp` at https://doc.rust-lang.org/nightly/src/core/num/f64.rs.html#1372
    fn hash<H: Hasher>(&self, state: &mut H) {
        let Self(value) = self;
        let mut bits = value.to_bits() as i64;
        bits ^= (((bits >> 63) as u64) >> 1) as i64;
        bits.hash(state);
    }
}

impl Debug for Decimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(value) = self;
        match value.classify() {
            FpCategory::Nan => write!(f, "%"),
            FpCategory::Infinite => write!(
                f,
                "{}",
                if value.is_sign_positive() {
                    "+∞"
                } else {
                    "-∞"
                }
            ),
            _ => write!(f, "{value:?}"),
        }
    }
}

impl Display for Decimal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn from_integer() {
        let integer = Integer(42);
        let sut = Decimal::from_integer(integer);
        assert_eq!(sut, integer.into());
        assert_eq!(sut, Decimal(42.0));
        sut.is_negative();
    }

    #[test]
    fn from_decimal() {
        assert_eq!(Decimal::from(3.14), Decimal(3.14));
    }

    #[test]
    fn to_decimal() {
        let integer: Integer = Integer(42);
        assert_eq!(integer.to_decimal(), Decimal(42.0));
    }

    #[test]
    fn zero() {
        assert_eq!(Decimal::ZERO, Decimal(0.0));
        assert_eq!(-Decimal::ZERO, Decimal(-0.0));
    }

    #[test]
    fn neg() {
        let sut = -Decimal(2.5);
        assert_eq!(sut, Decimal(-2.5));
    }

    #[test]
    fn add() {
        let sut = Decimal(2.5) + Decimal(3.5);
        assert_eq!(sut, Decimal(6.0));
    }

    #[test]
    fn sub() {
        let sut = Decimal(5.0) - Decimal(2.5);
        assert_eq!(sut, Decimal(2.5));
    }

    #[test]
    fn mul() {
        let sut = Decimal(2.5) * Decimal(3.0);
        assert_eq!(sut, Decimal(7.5));
    }

    #[test]
    fn div() {
        let sut = Decimal(5.0) / Decimal(2.0);
        assert_eq!(sut, Decimal(2.5));
    }

    #[test]
    fn rem() {
        let sut = Decimal(5.5) % Decimal(2.0);
        assert_eq!(sut, Decimal(1.5));
    }

    #[test]
    fn eq() {
        let sut1 = Decimal(10.0);
        let sut2 = Decimal(10.0);
        assert_eq!(sut1, sut2);
    }

    #[test]
    fn ne() {
        let sut1 = Decimal(10.0);
        let sut2 = Decimal(20.0);
        assert_ne!(sut1, sut2);
    }

    #[test]
    fn lt() {
        let sut1 = Decimal(10.0);
        let sut2 = Decimal(20.0);
        assert!(sut1 < sut2);
    }

    #[test]
    fn le() {
        let sut1 = Decimal(10.0);
        let sut2 = Decimal(20.0);
        let sut3 = Decimal(10.0);
        assert!(sut1 <= sut2);
        assert!(sut1 <= sut3);
    }

    #[test]
    fn gt() {
        let sut1 = Decimal(20.0);
        let sut2 = Decimal(10.0);
        assert!(sut1 > sut2);
    }

    #[test]
    fn ge() {
        let sut1 = Decimal(20.0);
        let sut2 = Decimal(10.0);
        let sut3 = Decimal(20.0);
        assert!(sut1 >= sut2);
        assert!(sut1 >= sut3);
    }

    #[test]
    fn display() {
        let sut = Decimal(3.14);
        assert_eq!(format!("{}", sut), "3.14");

        let sut = Decimal(0.0);
        assert_eq!(format!("{}", sut), "0.0");
    }

    #[test]
    fn debug() {
        let sut = Decimal(3.14);
        assert_eq!(format!("{:?}", sut), "3.14");

        let sut = Decimal(0.0);
        assert_eq!(format!("{:?}", sut), "0.0");
    }
}
