use prusti_contracts::*;

#[requires(0 < n)]
#[ensures(result > 0)]
fn fib(n: i32) -> i32 {
    let mut k = n;
    let mut i = 1;
    let mut j = 1;
    while k > 2 {
        body_invariant!(i > 0 && j > 0);
        let tmp = i + j;
        j = i;
        i = tmp;
        k -= 1;
    }
    i
}

fn main() {
    let x = fib(10);
    assert!(x != 0);
}
