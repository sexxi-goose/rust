// run-pass
#![feature(capture_disjoint_fields)]
//~^ WARNING: the feature `capture_disjoint_fields` is incomplete
//~| NOTE: `#[warn(incomplete_features)]` on by default
//~| NOTE: see issue #53488 <https://github.com/rust-lang/rust/issues/53488>
#![feature(rustc_attrs)]

// FIXME(rust-lang/project-rfc-2229#24) Currently when feature `capture_disjoint_fields`
// is enabled we can't handle wild card in patterns.

struct Point {
    x: i32,
    y: i32,
    id: String,
}

fn structs() {
    let mut p = Point { x: 10, y: 10, id: String::new() };

    let c = || {
        let Point { x: ref mut x, y: _, id: moved_id } = p;

        println!("{}, {}", x, moved_id);
    };

    c();
    println!("{:?}", p.y);
}

fn tuples() {
    let mut t = (10, String::new(), (String::new(), 42));

    let c = || {
        let (ref mut x, ref ref_str, (moved_s, _)) = t;
        println!("{}, {} {}", x, ref_str, moved_s);
    };

    c();
    println!("{:?}", t.2.1);
}

fn main() {}
