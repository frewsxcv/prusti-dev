use prusti_contracts::*;

// generics: using typarams with different names, and using more-generic
// functions with specifications from less-generic functions

struct FooBar;

struct Number<S, T> {
    i: i32,
    s: S,
    t: T,
}

#[requires(arg.i >= 7000)]
#[ensures(arg.i >= old(arg.i) - 1001)]
fn test1<A, B>(arg: &mut Number<A, B>) {
    arg.i -= 1000;
}

#[requires(arg.i >= 9000)]
#[ensures(arg.i >= 8000)] //~ ERROR postcondition might not hold
fn test2a<C>(arg: &mut Number<C, i16>) {
    test1(arg);
}

#[requires(arg.i >= 8000)]
#[ensures(arg.i >= 7000)] //~ ERROR postcondition might not hold
fn test2b<D>(arg: &mut Number<i8, D>) {
    test1(arg);
}

#[requires(arg.i >= 9000)]
#[ensures(arg.i >= 7000)]
fn test3(arg: &mut Number<i8, i16>) {
    test2a(arg);
    test2b(arg);
}

fn main() {}
