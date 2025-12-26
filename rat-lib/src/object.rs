/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::any::Any;
use std::fmt::Debug;
use std::sync::Arc;

pub trait Opaque: Any + Debug + Send + Sync {}

impl<T> Opaque for T where T: Any + Debug + Send + Sync {}

#[derive(Clone)]
pub struct Object {
    inner: Arc<Box<dyn Opaque>>,
}

impl Object {
    pub fn new<T: Opaque>(value: T) -> Self {
        Self {
            inner: Arc::new(Box::new(value)),
        }
    }

    pub fn is<T: Opaque>(&self) -> bool {
        self.as_any().is::<T>()
    }

    pub fn downcast_ref<T: Opaque>(&self) -> Option<&T> {
        self.as_any().downcast_ref()
    }

    pub fn make_mut<T: Opaque + Clone>(&mut self) -> Option<&mut T> {
        if !self.is::<T>() {
            return None;
        }

        // ensure unique ownership
        if Arc::get_mut(&mut self.inner).is_none() {
            // unwrap here is safe since we ensured: `self.is::<T>()`
            let value = self.downcast_ref::<T>().cloned().unwrap();
            self.inner = Arc::new(Box::new(value));
        }

        // at this point unique ownership is granted
        let any: &mut dyn Any = Arc::get_mut(&mut self.inner).map(AsMut::as_mut).unwrap();
        any.downcast_mut()
    }

    pub fn unwrap_or_clone<T: Opaque + Clone>(self) -> Option<T> {
        if !self.is::<T>() {
            return None;
        }

        match Arc::try_unwrap(self.inner) {
            Ok(boxed_opaque) => {
                let boxed_any: Box<dyn Any> = boxed_opaque;
                boxed_any.downcast::<T>().ok().map(|v| *v)
            }
            Err(arc) => {
                let any: &dyn Any = arc.as_ref().as_ref();
                any.downcast_ref::<T>().cloned()
            }
        }
    }

    #[inline]
    fn as_any(&self) -> &dyn Any {
        self.inner.as_ref().as_ref()
    }
}

impl Debug for Object {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.inner)
    }
}

#[cfg(test)]
mod test {
    use super::Object;

    #[test]
    fn is() {
        let seed = String::from("it works");
        let sut = Object::new(seed.clone());
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

    #[test]
    fn unwrap_or_clone() {
        let seed = String::from("it works");
        let sut = Object::new(seed.clone());
        assert_eq!(sut.unwrap_or_clone::<String>(), Some(seed));
    }

    #[test]
    fn debug() {
        let seed = String::from("it works");
        let sut = Object::new(seed.clone());
        assert_eq!(format!("{seed:?}"), format!("{sut:?}"));
    }
}
