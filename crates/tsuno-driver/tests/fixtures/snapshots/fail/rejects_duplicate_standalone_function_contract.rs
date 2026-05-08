/*@
fn declared_twice(x: i32) -> i32
  req x == 1i32
  ens result == 2i32
;
*/

fn declared_twice(x: i32) -> i32
//@ req {x} == 1i32
//@ ens result == 2i32
{
    x + 1
}

fn main() {}
