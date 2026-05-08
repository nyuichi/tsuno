/*@
fn safe_callee(x: i32) -> i32
  req x == 7i32
  ens result == 8i32
;
*/

fn safe_callee(x: i32) -> i32 {
    x + 1
}

fn main() {
    let y = safe_callee(7);
    //@ assert {y} == 8i32;
}
