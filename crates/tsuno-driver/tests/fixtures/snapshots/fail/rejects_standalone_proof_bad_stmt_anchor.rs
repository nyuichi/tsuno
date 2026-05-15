/*@
fn target() -> i32
  ens result == 1i32
{
  at stmt #9 {
    assert true;
  }
}
*/

fn target() -> i32 {
    1
}

fn main() {
    let _ = target();
}
