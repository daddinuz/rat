/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use std::collections::HashMap;
use std::error::Error;
use std::sync::RwLock;

use crossbeam::channel::{self, Receiver, Sender};

use crate::expression::Expression;
use crate::symbol::Symbol;

#[derive(Default)]
pub struct Globals {
    pub broker: Broker,
}

impl Globals {
    pub fn new() -> Self {
        Default::default()
    }
}

#[derive(Default)]
pub struct Broker {
    channels: RwLock<HashMap<Symbol, Channel>>,
}

impl Broker {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn send(&self, topic: Symbol, expression: Expression) -> Result<(), impl Error> {
        // IMPORTANT: we must release any lock before performing send or recv operations.
        // keeping any lock active while performing a recv operation may lead to deadlocks.
        // we must to minimize the scope of active locks.

        let sender = 'block: {
            // optimistically try to get the channel if it exists.
            if let Some(channel) = self.channels.read().unwrap().get(&topic) {
                break 'block channel.sender.clone();
            }

            // if it does not exist, create it.
            self.channels
                .write()
                .unwrap()
                .entry(topic)
                .or_default()
                .sender
                .clone()
        };

        sender.send(expression)
    }

    pub fn recv(&self, topic: Symbol) -> Result<Expression, impl Error> {
        // IMPORTANT: we must release any lock before performing send or recv operations.
        // keeping any lock active while performing a recv operation may lead to deadlocks.
        // we must to minimize the scope of active locks.

        let receiver = 'block: {
            // optimistically try to get the channel if it exists.
            if let Some(channel) = self.channels.read().unwrap().get(&topic) {
                break 'block channel.receiver.clone();
            }

            // if it does not exist, create it.
            self.channels
                .write()
                .unwrap()
                .entry(topic)
                .or_default()
                .receiver
                .clone()
        };

        receiver.recv()
    }
}

struct Channel {
    sender: Sender<Expression>,
    receiver: Receiver<Expression>,
}

impl Default for Channel {
    fn default() -> Self {
        let (sender, receiver) = channel::unbounded();
        Self { sender, receiver }
    }
}
