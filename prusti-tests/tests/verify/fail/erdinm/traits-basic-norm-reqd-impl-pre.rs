use prusti_contracts::*;

trait Percentage {
    #[requires(arg <= 100)]
    fn set(&mut self, arg: u8);
}

struct Effective {}

impl Percentage for Effective {
    fn set(&mut self, arg: u8) {
        assert!(arg <= 99); //~ ERROR the asserted expression might not hold
    }
}

fn main() {}
