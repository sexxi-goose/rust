// run-pas

#![feature(capture_disjoint_fields)]
//~^ WARNING: the feature `capture_disjoint_fields` is incomplete
//~| NOTE: `#[warn(incomplete_features)]` on by default
//~| NOTE: see issue #53488 <https://github.com/rust-lang/rust/issues/53488>

// FIXME(rust-lang/project-rfc-2229#24) Currently when feature `capture_disjoint_fields`
// is enabled we can't handle wild card in patterns.

enum Info {
    Point(i32, i32, String),
    Meta(String, Vec<(i32, i32)>)
}

fn multi_variant_enum() {
    let point = Info::Point(10, -10, "1".into());

    let vec = Vec::new();
    let meta = Info::Meta("meta".into(), vec);

    let c = || {
    if let Info::Point(_, _, str) = point {
            println!("{}", str);
        }

        if let Info::Meta(_, v) = meta {
            println!("{:?}", v);
        }
    };

    c();
}

enum SingleVariant {
    Point(i32, i32, String),
}

fn single_variant_enum() {
    let point = SingleVariant::Point(10, -10, "1".into());

    let c = || {
        let SingleVariant::Point(_, _, str) = point;
        println!("{}", str);
    };

    c();
    let SingleVariant::Point(a, b, _) = point;
    println!("{} {}", a, b);
}

fn main() {}
