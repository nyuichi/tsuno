/*@
enum List<T> {
    Nil,
    Cons(T, List<T>),
}

fn bad(xs: List<i32>)
  req true
  ens true
{
    match xs {
        List::Nil => {
            assert true;
        }
        List::Cons(_, xs0) => {
            bad(xs);
        }
    }
}
*/

fn main() {}
