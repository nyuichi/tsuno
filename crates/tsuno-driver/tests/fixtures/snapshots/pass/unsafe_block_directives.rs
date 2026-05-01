/*@
fn keeps_value(x: i32)
  req x == 7
  ens x == 7
{
    assume false;
}
*/

fn unsafe_block_directives() {
    let x = 7_i32;
    unsafe {
        let y = x;
        //@ let Y = {y};
        //@ assert {y} == 7;
        //@ assert Y == 7;
        //@ assume Y > 0;
        //@ keeps_value(Y);
        let _z = y;
    }
}

fn main() {}
