#![feature(capture_disjoint_fields)]
//~^ WARNING: the feature `capture_disjoint_fields` is incomplete

struct Point {
    x: i32,
    y: i32,
}

fn main() {
    let p = Point { x: 2, y: 3 };
    let c = || {
        let x = p.x;
        //~^ WARN
        let y = p.y;
        //~^ WARN
    };
    c();
}