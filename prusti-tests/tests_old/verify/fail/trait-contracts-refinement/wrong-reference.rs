use prusti_contracts::*;

trait Foo {  //~ ERROR no method 'bar' in super trait
    fn foo(&self, arg: i32) -> bool;
}

#[refine_requires(Foo::bar = "arg > 0")]
trait Sub: Foo {}

struct Dummy { }

impl Foo for Dummy {
    fn foo(&self, arg: i32) -> bool {
        arg > 5
    }
}

impl Sub for Dummy { }

fn test_foo(d: &Dummy) {
    assert!(d.foo(6));
}

fn main() {}
