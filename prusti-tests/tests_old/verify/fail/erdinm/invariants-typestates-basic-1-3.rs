use prusti_contracts::*;

use std::marker::PhantomData;

struct Neg;
struct Pos;

#[invariant(S == Neg ~~> self.i < 0)]
//#[invariant(S == Pos ~~> self.i > 0)]
struct Number<S> {
    i: i32,
    s: PhantomData<S>,
}

impl<X> Number<X> {
    #[ensures(self.i >= -1 && self.i <= 1)]
    fn to_sign(&mut self) {
        if self.i <= -1 {
            self.i = -1;
        } else if self.i >= 1 {
            self.i = 1;
        }
    }
}

fn test1(n: Number<Neg>) {
    let mut n = n;
    n.to_sign();
    assert!(n.i == -1);
}

fn test2(n: Number<Pos>) {
    let mut n = n;
    n.to_sign();
    assert!(n.i == 1); //~ ERROR the asserted expression might not hold
}

fn main() {}
