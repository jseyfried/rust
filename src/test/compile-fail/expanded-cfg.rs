// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(custom_attribute)]

macro_rules! mac {
    {} => {
        #[cfg(attr)]
        mod m {
            #[lang_item]
            fn f() {}

            #[cfg_attr(target_thread_local, custom)]
            fn g() {}

            unconfigured_invocation!();
        }

        #[cfg(target_thread_local)] //~ ERROR experimental and subject to change
        macro_rules! foo { () => {} }

        #[cfg(attr)]
        macro_rules! foo { () => { compile error } }

        foo!();
    }
}

mac! {}
