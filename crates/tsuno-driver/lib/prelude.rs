/*@
enum Nat {
    Zero,
    Succ(Nat),
}

enum List<T> {
    Nil,
    Cons(T, List<T>),
}

fn nat_add(x: Nat, y: Nat) -> Nat {
    match x {
        Nat::Zero => y,
        Nat::Succ(x0) => Nat::Succ(nat_add(x0, y)),
    }
}

fn nat_to_i32(n: Nat) -> i32 {
    match n {
        Nat::Zero => 0i32,
        Nat::Succ(n0) => 1i32 + nat_to_i32(n0),
    }
}

fn list_len(xs: List<i32>) -> Nat {
    match xs {
        List::Nil => Nat::Zero,
        List::Cons(_, xs0) => Nat::Succ(list_len(xs0)),
    }
}

fn list_append(xs: List<i32>, ys: List<i32>) -> List<i32> {
    match xs {
        List::Nil => ys,
        List::Cons(x, xs0) => List::Cons(x, list_append(xs0, ys)),
    }
}

fn nat_add_zero_right(n: Nat)
  req true
  ens nat_add(n, Nat::Zero) == n
{
    match n {
        Nat::Zero => {
            assert nat_add(n, Nat::Zero) == n;
        }
        Nat::Succ(n0) => {
            nat_add_zero_right(n0);
            assert nat_add(n, Nat::Zero) == n;
        }
    }
}

fn nat_add_assoc(x: Nat, y: Nat, z: Nat)
  req true
  ens nat_add(nat_add(x, y), z) == nat_add(x, nat_add(y, z))
{
    match x {
        Nat::Zero => {
            assert nat_add(nat_add(x, y), z) == nat_add(x, nat_add(y, z));
        }
        Nat::Succ(x0) => {
            nat_add_assoc(x0, y, z);
            assert nat_add(nat_add(x, y), z) == nat_add(x, nat_add(y, z));
        }
    }
}

fn list_append_nil_right(xs: List<i32>)
  req true
  ens list_append(xs, List::<i32>::Nil) == xs
{
    match xs {
        List::Nil => {
            assert list_append(xs, List::<i32>::Nil) == xs;
        }
        List::Cons(_, xs0) => {
            list_append_nil_right(xs0);
            assert list_append(xs, List::<i32>::Nil) == xs;
        }
    }
}

fn list_append_assoc(xs: List<i32>, ys: List<i32>, zs: List<i32>)
  req true
  ens list_append(list_append(xs, ys), zs) == list_append(xs, list_append(ys, zs))
{
    match xs {
        List::Nil => {
            assert list_append(list_append(xs, ys), zs) == list_append(xs, list_append(ys, zs));
        }
        List::Cons(_, xs0) => {
            list_append_assoc(xs0, ys, zs);
            assert list_append(list_append(xs, ys), zs) == list_append(xs, list_append(ys, zs));
        }
    }
}

fn list_len_append(xs: List<i32>, ys: List<i32>)
  req true
  ens list_len(list_append(xs, ys)) == nat_add(list_len(xs), list_len(ys))
{
    match xs {
        List::Nil => {
            assert list_len(list_append(xs, ys)) == nat_add(list_len(xs), list_len(ys));
        }
        List::Cons(_, xs0) => {
            list_len_append(xs0, ys);
            assert list_len(list_append(xs, ys)) == nat_add(list_len(xs), list_len(ys));
        }
    }
}

fn seq_concat_assoc<T>(xs: Seq<T>, ys: Seq<T>, zs: Seq<T>)
  req true
  ens (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
{
    assert (xs ++ ys) ++ zs == xs ++ (ys ++ zs);
}

fn seq_concat_empty_right<T>(xs: Seq<T>)
  req true
  ens xs ++ [] == xs
{
    assert xs ++ [] == xs;
}
*/
