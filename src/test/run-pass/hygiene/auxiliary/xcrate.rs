// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(decl_macro)]
#![allow(unused)]

pub use bar::test;

extern crate std as foo;

pub fn f() {}

mod bar {
    pub fn g() {}
    use baz::h;

    pub macro test() {
        ::foo::cell::Cell::new(0);
        ::f();
        g();
        ::bar::h();
    }
}

mod baz {
    pub fn h() {}
}
