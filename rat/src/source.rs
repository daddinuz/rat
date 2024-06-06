/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::fmt::Display;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Origin {
    Path(Box<str>),
    Unknown,
}

impl Origin {
    pub fn as_str(&self) -> &str {
        match self {
            Origin::Path(path) => path,
            Origin::Unknown => "<unknown>",
        }
    }
}

impl AsRef<Origin> for Origin {
    fn as_ref(&self) -> &Origin {
        self
    }
}

impl Display for Origin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

const _: [(); 16] = [(); std::mem::size_of::<Origin>()];
