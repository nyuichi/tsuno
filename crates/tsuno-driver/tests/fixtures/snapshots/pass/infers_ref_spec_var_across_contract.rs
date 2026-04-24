fn read_ref(x: &i32) -> i32
//@ let V = *{x};
//@ req true
//@ ens V == result
{
    *x
}

fn main() {
    let x = 1;
    let _ = read_ref(&x);
}
