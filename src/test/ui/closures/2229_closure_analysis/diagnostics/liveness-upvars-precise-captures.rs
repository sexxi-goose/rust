// run-pass
#![warn(unused)]

#![feature(capture_disjoint_fields)]
//~^ WARNING: the feature `capture_disjoint_fields` is incomplete

#[derive(Debug)]
struct Point<'a> {
    x: i32,
    y: Option<&'a str>,
}

pub fn unintentional_copy_one() {
    let mut last = Point{ x:1, y:None };
    let mut f = move |s| {
        last.y = Some(s);
    };
    f("a");
    f("b");
    f("c");

}

fn main() {
    unintentional_copy_one();
}
