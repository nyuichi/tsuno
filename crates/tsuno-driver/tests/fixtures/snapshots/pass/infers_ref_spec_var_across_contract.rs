fn read_ref(x: &i32) -> i32
//@ req "?V == *{x}"
//@ ens "V == result"
{
    *x
}

fn main() {
    let x = 1;
    let _ = read_ref(&x);
}
