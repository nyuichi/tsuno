/*@
fn proves_42(x: i32)
  req true
  ens x == 42
{
    assume false;
}
*/

fn helper() {}

fn tail_value(x: i32) -> i32
//@ req {x} == 42
//@ ens {result} == 42
{
    helper();
    //@ assume {x} == 42;
    //@ assert {x} == 42;
    //@ assume {x} == 42;
    //@ proves_42({x});
    //@ assert {x} == 42;
    x
}

fn block_end(x: i32) {
    helper();
    //@ assume {x} == 42;
    //@ assert {x} == 42;
    //@ assume {x} == 42;
    //@ proves_42({x});
    //@ assert {x} == 42;
}

fn main() {
    let x = 42_i32;
    let y = tail_value(x);
    //@ assert {y} == 42;
    block_end(y);
}
