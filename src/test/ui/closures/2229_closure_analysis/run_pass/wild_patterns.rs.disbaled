// run-pass

#![feature(capture_disjoint_fields)]
//~^ WARNING: the feature `capture_disjoint_fields` is incomplete
//~| NOTE: `#[warn(incomplete_features)]` on by default
//~| NOTE: see issue #53488 <https://github.com/rust-lang/rust/issues/53488>

// Test to ensure that we can handle cases where
// let statements create no bindings are intialized
// using a Place expression
//
// FIXME(rust-lang/project-rfc-2229#24) Currently when feature `capture_disjoint_fields`
// is enabled we can't handle such cases.

struct Point {
    x: String,
    y: String,
}

fn wild_struct() {
    let p = Point { x: "12".to_string(), y: "20".to_string() };

    let c = || {
        let Point { x: _, y: _ } = p;
    };

    c();

    println!("{} {}", p.x, p.y);
}

fn wild_tuple() {
    let t = (String::new(), 10);

    let c = || {
        let (_, _) = t;
    };

    c();
    println!("{} {}", t.0, t.1);
}

fn main() {}
