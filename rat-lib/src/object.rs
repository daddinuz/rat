/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::Debug;
use std::sync::Arc;

use crate::r#abstract::{Abstract, AbstractObject};

#[derive(Clone)]
pub struct Object(Arc<AbstractObject>);

impl Object {
    pub fn new<T: Abstract>(value: T) -> Self {
        Self(Arc::new(AbstractObject::new(value)))
    }

    pub fn is<T: Abstract>(&self) -> bool {
        let Self(object) = self;
        object.is::<T>()
    }

    pub fn downcast_ref<T: Abstract>(&self) -> Option<&T> {
        let Self(object) = self;
        object.downcast_ref()
    }

    pub fn make_mut<T: Abstract>(&mut self) -> Option<&mut T> {
        let Self(object) = self;

        if !object.is::<T>() {
            return None;
        }

        Arc::make_mut(object).downcast_mut()
    }
}

impl Debug for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self(object) = self;
        write!(f, "{object:?}")
    }
}

#[cfg(test)]
mod test {
    use super::Object;

    #[test]
    fn is() {
        let sut = Object::new(String::from("it works"));
        assert!(sut.is::<String>());
    }

    #[test]
    fn downcast_ref() {
        let seed = String::from("it works");
        let sut = Object::new(seed.clone());
        assert_eq!(sut.downcast_ref::<String>(), Some(&seed));
    }

    #[test]
    fn make_mut() {
        let mut seed = String::from("it works");
        let mut sut = Object::new(seed.clone());
        assert_eq!(sut.make_mut::<String>(), Some(&mut seed));
    }
}
