use prusti_contracts::*;

struct Point {
  x: i32, y: i32
}

#[ensures(p.x == old(p.x) + s)]
#[ensures(p.y == old(p.y))]
fn shift_x(p: &mut Point, s: i32) {
  p.x = p.x + s
}

fn compress(mut segm: (Box<Point>, Box<Point>))
                    -> (Box<Point>, Box<Point>) {
  let diff = (*segm.0).x - (*segm.1).x + 1;
  shift_x(&mut segm.1, diff);
  assert!((*segm.0).x < (*segm.1).x);
  segm
}

fn client(mut p: Point, mut q: Point) {
    p.y = q.y;
    let s = q.x - p.x;
    shift_x(&mut p, s);
    assert!(p.x == q.x && p.y == q.y);
}

fn main() {}
