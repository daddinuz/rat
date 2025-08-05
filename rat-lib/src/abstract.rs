/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::any::Any;
use std::fmt::Debug;

pub trait Abstract: Any + Debug + Send + Sync {
    fn clone_into_box(&self) -> Box<dyn Abstract>;

    fn as_any(&self) -> &dyn Any;

    fn as_any_mut(&mut self) -> &mut dyn Any;
}

impl<T> Abstract for T
where
    T: Any + Clone + Debug + Send + Sync,
{
    fn clone_into_box(&self) -> Box<dyn Abstract> {
        Box::new(self.clone())
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

pub struct AbstractObject {
    inner: Box<dyn Abstract>,
}

impl AbstractObject {
    pub fn new<T: Abstract>(value: T) -> Self {
        Self {
            inner: Box::new(value),
        }
    }

    pub fn is<T>(&self) -> bool
    where
        T: Abstract,
    {
        self.inner.as_any().is::<T>()
    }

    pub fn downcast_ref<T>(&self) -> Option<&T>
    where
        T: Abstract,
    {
        self.inner.as_any().downcast_ref()
    }

    pub fn downcast_mut<T>(&mut self) -> Option<&mut T>
    where
        T: Abstract,
    {
        self.inner.as_any_mut().downcast_mut()
    }
}

impl Clone for AbstractObject {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone_into_box(),
        }
    }
}

impl Debug for AbstractObject {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}
