#![feature(capture_disjoint_fields)]
//~^ WARNING: the feature `capture_disjoint_fields` is incomplete
#![allow(unreachable_code)]

#[derive(Debug)]
struct Point {
    x: i32,
    y: i32,
}

pub fn f() {
    let mut c = Point{ x:1, y:0 };

    // Captured by value, but variable is dead on entry.
    (move || {
        c.x = 1;
        println!("{}", c.x);
    })();

    // Read and written to, but never actually used.
    (move || {
        c.x += 1;
    })();

    (move || {
        println!("{}", c.x);
        // Value is read by closure itself on later invocations.
        c.x += 1;
    })();
    let b = Box::new(42);
    (move || {
        println!("{}", c.x);
        // Never read because this is FnOnce closure.
        c.x += 1;
        drop(b);
    })();
}

#[derive(Debug)]
struct MyStruct<'a>  {
    x: Option<& 'a str>,
    y: i32,
}

pub fn nested() {
    let mut d = MyStruct{ x: None, y: 1};
    let mut e = MyStruct{ x: None, y: 1};
    (|| {
        (|| {
            d.x = Some("d1");
            d.x = Some("d2");
        })();
        (move || {
            e.x = Some("e1");
            e.x = Some("e2");
        })();
    })();
}

fn main() {}
