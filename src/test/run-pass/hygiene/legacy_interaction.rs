// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ignore-pretty pretty-printing is unhygienic

// aux-build:legacy_interaction.rs

#![feature(decl_macro)]
#[allow(unused)]

extern crate legacy_interaction;
// ^ defines
// ```rust
//  macro_rules! m {
//     () => {
//         f() // (1)
//         fn g() {} // (2)
//     }
// }
// ```rust

mod def_site {
    // Unless this macro opts out of hygiene, it shouldn't matter where it is invoked.
    pub macro m2() {
        ::legacy_interaction::m!();
        fn f() {} // We want (1) resolve to this, not to (3)
        g(); // We want this to resolve to (2)
    }
}

mod use_site {
    fn test() { ::def_site::m2!(); }
}

fn main() {}
