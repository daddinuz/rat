/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

macro_rules! binary_operator {
    ($type:ty, $($trait:ident :: $operation:ident),+ $(,)?) => {
        $(
            impl $trait for $type {
                type Output = Self;

                #[inline]
                fn $operation(self, Self(rhs): Self) -> Self::Output {
                    let Self(lhs) = self;
                    Self($trait::$operation(lhs, rhs))
                }
            }
        )+
    };
}

pub(crate) use binary_operator;

macro_rules! binary_assign_operator {
    ($type:ty, $($trait:ident :: $operation:ident),+ $(,)?) => {
        $(
            impl $trait for $type {
                #[inline]
                fn $operation(&mut self, Self(rhs): Self) {
                    let Self(lhs) = self;
                    $trait::$operation(lhs, rhs)
                }
            }
        )+
    };
}

pub(crate) use binary_assign_operator;

macro_rules! unary_operator {
    ($type:ty, $($trait:ident :: $operation:ident),+ $(,)?) => {
        $(
            impl $trait for $type {
                type Output = Self;

                #[inline]
                fn $operation(self) -> Self::Output {
                    let Self(inner) = self;
                    Self($trait::$operation(inner))
                }
            }
        )+
    };
}

pub(crate) use unary_operator;
