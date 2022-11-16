use prusti_contracts::*;

#[derive(Clone,Copy,PartialEq,Eq)]
struct A {
    i: i32,
}

#[pure]
fn get_value(_x: A, _y: A) -> A {
    _x
}

fn main() {
    let _a = A { i: 17 };
    let _b = A { i: 19 };
    let _x = get_value(_a, _b);
    assert!(_x == _a);
}
