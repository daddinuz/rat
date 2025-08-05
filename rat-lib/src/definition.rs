/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::sync::Arc;

use crate::dictionary::Dictionary;
use crate::visibility::Visibility;
use crate::word::Word;

#[derive(Clone, Debug)]
pub struct Definition {
    kind: DefinitionKind,
    visibility: Visibility,
}

impl Definition {
    #[inline]
    pub fn new(kind: DefinitionKind, visibility: Visibility) -> Self {
        Self { kind, visibility }
    }

    #[inline]
    pub fn new_expression(expression: Arc<[Word]>, visibility: Visibility) -> Self {
        Self::new(DefinitionKind::Expression(expression), visibility)
    }

    #[inline]
    pub fn new_dictionary(dictionary: Arc<Dictionary>, visibility: Visibility) -> Self {
        Self::new(DefinitionKind::Dictionary(dictionary), visibility)
    }

    #[inline]
    pub fn kind(&self) -> &DefinitionKind {
        &self.kind
    }

    #[inline]
    pub fn visibility(&self) -> Visibility {
        self.visibility
    }
}

#[derive(Clone, Debug)]
pub enum DefinitionKind {
    Expression(Arc<[Word]>),
    Dictionary(Arc<Dictionary>),
}

const _: () = crate::is_thread_safe::<Definition>();
const _: [(); 3 * std::mem::size_of::<usize>()] = [(); std::mem::size_of::<Definition>()];
