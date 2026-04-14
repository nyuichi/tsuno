fn assume_prunes_when_not_entailed(x: i32) {
    //@ assume {x} == 0;
    impossible();
}

fn impossible()
//@ req false
//@ ens true
{
}

fn main() {}
