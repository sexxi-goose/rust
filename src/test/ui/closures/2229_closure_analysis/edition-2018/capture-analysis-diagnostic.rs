// edition:2018
#![feature(rustc_attrs)]

struct S(i32);

fn foo() {
    let b = Box::new(S(10));

    let c = #[rustc_capture_analysis]
    //~^ ERROR: attributes on expressions are experimental
    //~| NOTE: see issue #15701 <https://github.com/rust-lang/rust/issues/15701>
    || {
    //~^ First Pass analysis includes:
    //~| Min Capture analysis includes:
        let _b = b.0;
        //~^ NOTE: 15:18: 15:21: Min Capture b[] -> ImmBorrow
        //~| NOTE: 15:18: 15:21: Capturing b[Deref,(0, 0)] -> ImmBorrow
    };

    c();
}

fn main() {
    foo();
}
