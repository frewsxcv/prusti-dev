use prusti_contracts::*;

fn test1(n: u32) -> u32 {
    let mut i = 0;
    while i < n {
        i += 1;
    }
    i
}

#[requires(n >= 0)]
#[ensures(result == old(n))]
fn test2(n: i32) -> i32 {
    let mut res = 0;
    let mut ia = 0;

    while ia < n {
        body_invariant!(res == ia);
        body_invariant!(ia < n);
        res += 1;
        ia += 1;
    }

    res
}

fn main() {}
