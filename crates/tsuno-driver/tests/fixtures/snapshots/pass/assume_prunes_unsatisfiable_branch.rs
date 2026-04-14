fn assume_prunes_unsatisfiable_branch(x: i32)
//@ req {x} != 0
//@ ens true
{
    //@ assume {x} == 0;
    impossible();
}

fn impossible()
//@ req false
//@ ens true
{
}

fn main() {}
