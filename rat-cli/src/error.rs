/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::error::Error;
use std::fmt::{Debug, Display, Error as FmtError, Formatter, Result as FmtResult};
use std::io::Error as IoError;

use rustyline::error::ReadlineError;

use rat::parser::ParseError;

pub struct CliError(Box<dyn Error>);

impl From<ReadlineError> for CliError {
    fn from(error: ReadlineError) -> Self {
        Self(error.into())
    }
}

impl From<ParseError> for CliError {
    fn from(error: ParseError) -> Self {
        Self(error.into())
    }
}

impl From<FmtError> for CliError {
    fn from(error: FmtError) -> Self {
        Self(error.into())
    }
}

impl From<IoError> for CliError {
    fn from(error: IoError) -> Self {
        Self(error.into())
    }
}

impl From<String> for CliError {
    fn from(message: String) -> Self {
        Self(message.into())
    }
}

impl From<&str> for CliError {
    fn from(message: &str) -> Self {
        Self(message.into())
    }
}

impl Debug for CliError {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

impl Display for CliError {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        write!(f, "{}", self.0)
    }
}

impl Error for CliError {}

pub trait Report {
    fn report(self);

    fn report_if(self, predicate: impl FnOnce(&Self) -> bool)
    where
        Self: Sized,
    {
        if predicate(&self) {
            self.report()
        }
    }
}

impl<E: Error> Report for E {
    fn report(self) {
        eprintln!("{self}");
    }
}

pub trait Consume {
    fn consume(self);
}

impl<T> Consume for T {
    fn consume(self) {}
}
