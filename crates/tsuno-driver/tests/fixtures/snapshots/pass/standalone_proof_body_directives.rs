/*@
fn count_to(n: i32) -> ()
  req n >= 0i32
  ens true
{
  at stmt #0 {
    let initial = {n};
    assert initial == {n};
  }
  at loop #0 {
    inv 0i32 <= {x} && {x} <= {n};
  }
  at stmt #2 {
    assert true;
  }
  at exit #0 {
    assert true;
  }
}
*/

fn count_to(n: i32) {
    let mut x = 0;
    while x < n {
        x = x + 1;
    }
}

fn main() {
    count_to(3);
}
