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
                fn $operation(self, rhs: Self) -> Self::Output {
                    Self($trait::$operation(self.0, rhs.0))
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
                fn $operation(&mut self, rhs: Self) {
                    $trait::$operation(&mut self.0, rhs.0)
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
                    Self($trait::$operation(self.0))
                }
            }
        )+
    };
}

pub(crate) use unary_operator;
