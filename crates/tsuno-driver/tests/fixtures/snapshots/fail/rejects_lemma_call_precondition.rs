/*@
fn need_zero(x: i32)
  req "{x} == 0"
  ens "true"
{
    assert "{x} == 0";
}
*/

fn main() {
    let x = 1_i32;
    //@ need_zero(x);
    let _ = ();
}
