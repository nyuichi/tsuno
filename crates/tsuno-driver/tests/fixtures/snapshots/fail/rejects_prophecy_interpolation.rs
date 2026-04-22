fn set_to_two(x: &mut i32)
//@ req true
//@ ens __prophecy({x}) == 2
{
    *x = 3;
}

fn main() {}
