fn set_to_two(x: &mut i32)
//@ req true
//@ ens {x}.fin == 2
{
    *x = 3;
}

fn main() {}
