#![warn(unused)]
#![allow(unreachable_code)]
#![feature(capture_disjoint_fields)]

#[derive(Debug)]
struct Point<'a> {
    x: i32,
    y: Option<&'a str>,
}

pub fn unintentional_copy_one() {
    let mut last = Point{ x:1, y:None };
    let mut f = |s| {
        last.y = Some(s); 
    };
    f("a");
    f("b");
    f("c");
    dbg!(last.y.unwrap());
}

fn main() {}