/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use crossbeam::channel::{self, Receiver, Sender};

use std::error::Error;
use std::fmt::{Debug, Display};
use std::hash::Hash;
use std::sync::Arc;
use std::thread::{self, ThreadId};

use crate::effect::Effect;
use crate::evaluate::Evaluate;
use crate::evaluator::Evaluator;
use crate::expression::Expression;
use crate::quote::Quote;

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Channel {
    inner: Arc<Inner>,
}

impl Channel {
    pub fn spawn(quote: Quote) -> Self {
        let (send, consume) = channel::unbounded();
        let (produce, receive) = channel::unbounded();

        let handle = thread::spawn(move || {
            let mut evaluator = Evaluator {
                stack: Vec::new(),
                channel: Some((produce, consume)),
            };
            evaluator.evaluate(quote)
        });

        Self {
            inner: Arc::new(Inner {
                sender: send,
                receiver: receive,
                identity: handle.thread().id(),
            }),
        }
    }

    pub fn send(&self, expr: Expression) -> Result<(), impl Error> {
        self.inner.sender.send(expr)
    }

    pub fn recv(&self) -> Result<Expression, impl Error> {
        self.inner.receiver.recv()
    }
}

impl Evaluate<&mut Evaluator> for Channel {
    type Output = Result<(), Effect>;

    fn evaluate(self, evaluator: &mut Evaluator) -> Self::Output {
        evaluator.stack.push(Expression::Channel(self));
        Ok(())
    }
}

impl Display for Channel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(self, f)
    }
}

impl Debug for Channel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "↯{:?}", self.inner.identity)
    }
}

struct Inner {
    sender: Sender<Expression>,
    receiver: Receiver<Expression>,
    identity: ThreadId,
}

impl PartialEq for Inner {
    fn eq(&self, other: &Self) -> bool {
        self.identity == other.identity
    }
}

impl Eq for Inner {}

impl Hash for Inner {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.identity.hash(state)
    }
}
