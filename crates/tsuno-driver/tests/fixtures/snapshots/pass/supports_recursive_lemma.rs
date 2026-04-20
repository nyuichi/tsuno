/*@
fn len(xs: List<i32>) -> i32 {
    match xs {
        List::Nil => 0i32,
        List::Cons(_, xs0) => 1i32 + len(xs0),
    }
}

fn append(xs: List<i32>, ys: List<i32>) -> List<i32> {
    match xs {
        List::Nil => ys,
        List::Cons(x, xs0) => List::Cons(x, append(xs0, ys)),
    }
}

fn append_len(xs: List<i32>, ys: List<i32>)
  req true
  ens len(append(xs, ys)) == len(xs) + len(ys)
{
    match xs {
        List::Nil => {
            assert len(append(xs, ys)) == len(xs) + len(ys);
        }
        List::Cons(_, xs0) => {
            append_len(xs0, ys);
            assert len(append(xs, ys)) == len(xs) + len(ys);
        }
    }
}
*/

fn main() {
    //@ append_len(List::Cons(0i32, List::Nil), List::Cons(1i32, List::Nil));
    //@ assert len(append(List::Cons(0i32, List::Nil), List::Cons(1i32, List::Nil))) == 2i32;
}
