/*@
fn bad(x: i32)
  req true
  ens true
{
    assume true;
    assert false;
}
*/

fn main() {
    let x = 0_i32;
    //@ bad({x});
    let _ = ();
}
