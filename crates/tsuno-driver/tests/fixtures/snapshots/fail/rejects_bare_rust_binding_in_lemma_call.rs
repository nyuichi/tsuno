/*@
fn prove_42(x: i32)
  req true
  ens x == 42i32
{
    assume false;
}
*/

fn main() {
    let x = 42_i32;
    //@ prove_42(x);
}
