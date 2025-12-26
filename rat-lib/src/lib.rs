/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

mod codegen;

pub mod boolean;
pub mod character;
pub mod component;
pub mod context;
pub mod decimal;
pub mod definition;
pub mod dictionary;
pub mod identifier;
pub mod integer;
pub mod object;
pub mod parser;
pub mod prelude;
pub mod quote;
pub mod string;
pub mod symbol;
pub mod verb;
pub mod visibility;
pub mod word;

use std::env;
use std::path::Path;
use std::sync::LazyLock;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

#[allow(deprecated)]
pub fn home_dir() -> &'static Path {
    static HOME_DIR: LazyLock<Box<Path>> = LazyLock::new(|| {
        let mut home_dir = env::home_dir().unwrap_or_default();
        home_dir.push(".rat");
        home_dir.into()
    });

    &HOME_DIR
}

#[allow(dead_code)]
const fn is_thread_safe<T: Send + Sync>() {}
