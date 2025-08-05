/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

use rat::context::Context;
use rat::integer::Integer;
use rat::object::Object;
use rat::prelude::{add, binrec, decr, dup, is_lt, pop, say};
use rat::quote::Quote;
use rat::verb::Verb;
use rat::word::Word;

fn main() {
    let main = Quote::from([
        Word::Integer(Integer(37)),
        Word::Object(Object::new(Quote::from([
            Word::Integer(Integer(3)),
            Word::Verb(Verb(is_lt)),
        ]))),
        Word::Object(Object::new(Quote::from([
            Word::Verb(Verb(pop)),
            Word::Integer(Integer(1)),
        ]))),
        Word::Object(Object::new(Quote::from([
            Word::Verb(Verb(decr)),
            Word::Verb(Verb(dup)),
            Word::Verb(Verb(decr)),
        ]))),
        Word::Object(Object::new(Quote::from([Word::Verb(Verb(add))]))),
        Word::Verb(Verb(binrec)),
        Word::Verb(Verb(say)),
    ]);

    let mut context = Context::new();
    context.unquote(&main).unwrap();
}
