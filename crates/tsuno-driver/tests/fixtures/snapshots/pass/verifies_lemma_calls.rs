/*@
fn proves_42(x: i32)
  req "true"
  ens "x == 42"
{
    assume "false";
}

fn nested(x: i32)
  req "true"
  ens "x == 42"
{
    proves_42(x);
    assert "x == 42";
}
*/

fn main() {
    let x = 42_i32;
    //@ nested(x);
    //@ assert "{x} == 42"
    let _ = ();
}
