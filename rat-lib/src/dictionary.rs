/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::borrow::Borrow;
use std::hash::Hash;
use std::ptr;

use hashbrown::HashMap;

use crate::component::OwnedComponent;
use crate::definition::{Definition, DefinitionKind};
use crate::identifier::Identifier;
use crate::visibility::Visibility;
use crate::word::Word;

#[derive(Clone, Debug, Default)]
pub struct Dictionary {
    definitions: HashMap<OwnedComponent, Definition>,
}

const _: () = crate::is_thread_safe::<Dictionary>();
const _: [(); 5 * std::mem::size_of::<usize>()] = [(); std::mem::size_of::<Dictionary>()];

impl FromIterator<(OwnedComponent, Definition)> for Dictionary {
    #[inline]
    fn from_iter<T: IntoIterator<Item = (OwnedComponent, Definition)>>(iter: T) -> Self {
        Self {
            definitions: iter.into_iter().collect(),
        }
    }
}

impl<const N: usize> From<[(OwnedComponent, Definition); N]> for Dictionary {
    #[inline]
    fn from(value: [(OwnedComponent, Definition); N]) -> Self {
        Self {
            definitions: value.into(),
        }
    }
}

impl Dictionary {
    #[inline]
    pub fn new() -> Self {
        Self {
            definitions: HashMap::new(),
        }
    }

    #[inline]
    pub fn insert(
        &mut self,
        component: OwnedComponent,
        definition: Definition,
    ) -> Option<Definition> {
        self.definitions.insert(component, definition)
    }

    #[inline]
    pub fn get<T>(&self, component: &T) -> Option<&Definition>
    where
        OwnedComponent: Borrow<T>,
        T: Eq + Hash + ?Sized,
    {
        self.definitions.get(component)
    }

    pub fn lookup(&self, identifier: &Identifier) -> Option<&[Word]> {
        let mut components = identifier.components();
        let mut dictionary = self;

        while let Some(component) = components.next() {
            let definition = dictionary.get(component)?;

            if !ptr::eq(self, dictionary) && definition.visibility() == Visibility::Intern {
                break;
            }

            match definition.kind() {
                DefinitionKind::Expression(expression) => {
                    if components.next().is_some() {
                        break;
                    }

                    return Some(expression);
                }
                DefinitionKind::Dictionary(next_dictionary) => dictionary = next_dictionary,
            }
        }

        None
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = (&OwnedComponent, &Definition)> {
        self.definitions.iter()
    }

    #[inline]
    pub fn retain<F>(&mut self, f: F)
    where
        F: FnMut(&OwnedComponent, &mut Definition) -> bool,
    {
        self.definitions.retain(f);
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.definitions.is_empty()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.definitions.len()
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.definitions.capacity()
    }
}
