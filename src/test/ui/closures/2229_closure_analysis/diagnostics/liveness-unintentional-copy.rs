#![feature(capture_disjoint_fields)]
//~^ WARNING: the feature `capture_disjoint_fields` is incomplete
#![warn(unused)]

#[derive(Debug)]
struct MyStruct {
    a: i32,
    b: i32,
}

pub fn unintentional_copy_one() {
    let mut last = MyStruct{ a: 1, b: 1};
    let mut f = move |s| {
        last.a = s; //~  WARN value assigned to `last.b` is never read
                        //~| WARN unused variable: `last.b`
    };
    f(2);
    f(3);
    f(4);
}

pub fn unintentional_copy_two() {
    let mut sum = MyStruct{ a: 1, b: 0};
    (1..10).for_each(move |x| {
        sum.b += x; //~ WARN unused variable: `sum.a`
    });
}

fn main() {
    unintentional_copy_one();
    unintentional_copy_two();
}
