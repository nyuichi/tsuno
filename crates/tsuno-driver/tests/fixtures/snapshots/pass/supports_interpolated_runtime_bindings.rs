/*@
fn prove_42(x: i32)
  req true
  ens x == 42i32
{
    assume false;
}
*/

fn id(x: i32) -> i32
//@ req {x} == 42i32
//@ ens {result} == {x}
{
    //@ assume {x} == 42i32;
    //@ assert {x} == 42i32;
    //@ prove_42({x});
    x
}

fn count_to(n: i32)
//@ req 0i32 <= {n}
//@ ens true
{
    let mut x = 0_i32;
    while x < n
      //@ inv 0i32 <= {x} && {x} <= {n}
    {
        x += 1;
    }
}

fn main() {
    let x = id(42_i32);
    //@ assert {x} == 42i32;
    count_to(3_i32);
}
