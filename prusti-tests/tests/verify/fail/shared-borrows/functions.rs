use prusti_contracts::*;

fn borrow(_x: &u32) {}

fn borrow2(_x: &u32, _y: &u32) {}

pub fn test1() {
    let a = 5;
    let x = &a;
    borrow(x);
    assert!(false); //~ ERROR the asserted expression might not hold
}

pub fn test2(x: &u32) {
    let a = *x;
    let y = &a;
    borrow(y);
    assert!(false); //~ ERROR the asserted expression might not hold
}

pub fn test3(x: &u32) {
    borrow(x);
    assert!(false); //~ ERROR the asserted expression might not hold
}

pub fn test4(x: &mut u32) {
    borrow(x);
    assert!(false); //~ ERROR the asserted expression might not hold
}

pub fn test5() {
    let a = 5;
    let b = 6;
    let x = &a;
    let y = &b;
    borrow2(x, y);
    assert!(false); //~ ERROR the asserted expression might not hold
}

#[requires(*x == 5)]
#[ensures(*x == 5)]
pub fn test6(x: &u32) {
    assert!(false); //~ ERROR the asserted expression might not hold
}

#[ensures(*x == old(*x))]
pub fn test7(x: &u32) {
    assert!(false); //~ ERROR the asserted expression might not hold
}

pub fn test8() {
    let a = 5;
    borrow(&a);
    assert!(a == 5);
    let x = &a;
    borrow(&a);
    borrow2(x, &a);
    assert!(a == 5);
    assert!(*x == 5);
    assert!(false); //~ ERROR the asserted expression might not hold
}

fn main() {
}
