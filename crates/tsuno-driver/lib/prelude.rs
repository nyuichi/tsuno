/*@
enum Option<T> {
    None,
    Some(T),
}

struct Provenance {
    base: usize,
}

struct Ptr {
    addr: usize,
    prov: Option<Provenance>,
    ty: RustTy,
}

struct Ref<T> {
    deref: T,
    ptr: Ptr,
}

struct Mut<T> {
    cur: T,
    fin: T,
    ptr: Ptr,
}

struct Layout {
    size: usize,
    align: usize,
} where align != 0usize &&
    (align & (align - 1usize)) == 0usize &&
    size + align - 1usize <= (isize::MAX as usize);

def layout_of(ty: RustTy) -> Layout;

lem layout_of_i32()
  req true
  ens layout_of({type i32}) == Layout { size: 4usize, align: 4usize }
{
    assume false;
}

unsafe fn core::intrinsics::read_via_copy<T>(ptr: *const T) -> T
  raw req *ptr |-?-> Option::<T>::Some(?old) * Own::<T>(old)
  raw ens *ptr |-?-> Option::<T>::Some(old)
  ens result == old
;

unsafe fn core::intrinsics::write_via_move<T>(ptr: *mut T, value: T) -> ()
  raw req *ptr |-?-> ?old * Own::<T>(value)
  raw ens *ptr |-?-> Option::<T>::Some(value) * Own::<T>(value)
;

unsafe lem own_i32(v: i32)
  raw req emp
  raw ens Own::<i32>(v)
{
    assume false;
}

unsafe lem drop_own_i32(v: i32)
  raw req Own::<i32>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_bool(v: bool)
  raw req emp
  raw ens Own::<bool>(v)
{
    assume false;
}

unsafe lem drop_own_bool(v: bool)
  raw req Own::<bool>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_i8(v: i8)
  raw req emp
  raw ens Own::<i8>(v)
{
    assume false;
}

unsafe lem drop_own_i8(v: i8)
  raw req Own::<i8>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_i16(v: i16)
  raw req emp
  raw ens Own::<i16>(v)
{
    assume false;
}

unsafe lem drop_own_i16(v: i16)
  raw req Own::<i16>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_i64(v: i64)
  raw req emp
  raw ens Own::<i64>(v)
{
    assume false;
}

unsafe lem drop_own_i64(v: i64)
  raw req Own::<i64>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_isize(v: isize)
  raw req emp
  raw ens Own::<isize>(v)
{
    assume false;
}

unsafe lem drop_own_isize(v: isize)
  raw req Own::<isize>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_u8(v: u8)
  raw req emp
  raw ens Own::<u8>(v)
{
    assume false;
}

unsafe lem drop_own_u8(v: u8)
  raw req Own::<u8>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_u16(v: u16)
  raw req emp
  raw ens Own::<u16>(v)
{
    assume false;
}

unsafe lem drop_own_u16(v: u16)
  raw req Own::<u16>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_u32(v: u32)
  raw req emp
  raw ens Own::<u32>(v)
{
    assume false;
}

unsafe lem drop_own_u32(v: u32)
  raw req Own::<u32>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_u64(v: u64)
  raw req emp
  raw ens Own::<u64>(v)
{
    assume false;
}

unsafe lem drop_own_u64(v: u64)
  raw req Own::<u64>(v)
  raw ens emp
{
    assume false;
}

unsafe lem own_usize(v: usize)
  raw req emp
  raw ens Own::<usize>(v)
{
    assume false;
}

unsafe lem drop_own_usize(v: usize)
  raw req Own::<usize>(v)
  raw ens emp
{
    assume false;
}

enum Nat {
    Zero,
    Succ(Nat),
}

enum List<T> {
    Nil,
    Cons(T, List<T>),
}

def nat_add(x: Nat, y: Nat) -> Nat =
    match x {
        Nat::Zero => y,
        Nat::Succ(x0) => Nat::Succ(nat_add(x0, y)),
    }

def nat_bit0(n: Nat) -> Nat =
    nat_add(n, n)

def nat_bit1(n: Nat) -> Nat =
    Nat::Succ(nat_bit0(n))

def nat_to_i32(n: Nat) -> i32 =
    match n {
        Nat::Zero => 0i32,
        Nat::Succ(n0) => 1i32 + nat_to_i32(n0),
    }

def list_len(xs: List<i32>) -> Nat =
    match xs {
        List::Nil => Nat::Zero,
        List::Cons(_, xs0) => Nat::Succ(list_len(xs0)),
    }

def list_append(xs: List<i32>, ys: List<i32>) -> List<i32> =
    match xs {
        List::Nil => ys,
        List::Cons(x, xs0) => List::Cons(x, list_append(xs0, ys)),
    }

lem nat_add_zero_right(n: Nat)
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

lem nat_add_assoc(x: Nat, y: Nat, z: Nat)
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

lem list_append_nil_right(xs: List<i32>)
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

lem list_append_assoc(xs: List<i32>, ys: List<i32>, zs: List<i32>)
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

lem list_len_append(xs: List<i32>, ys: List<i32>)
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

def seq_rev_prefix<T>(xs: Seq<T>, n: Nat, acc: Seq<T>) -> Seq<T> =
    match n {
        Nat::Zero => acc,
        Nat::Succ(m) => seq_rev_prefix(xs, m, acc ++ [xs[m]]),
    }

def seq_rev<T>(xs: Seq<T>) -> Seq<T> =
    seq_rev_prefix(xs, seq_len(xs), [])

lem seq_rev_empty<T>(xs: Seq<T>)
  req xs == []
  ens seq_rev(xs) == []
{
    assert seq_rev(xs) == [];
}

lem seq_concat_assoc<T>(xs: Seq<T>, ys: Seq<T>, zs: Seq<T>)
  req true
  ens (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
{
    assert (xs ++ ys) ++ zs == xs ++ (ys ++ zs);
}

lem seq_concat_empty_right<T>(xs: Seq<T>)
  req true
  ens xs ++ [] == xs
{
    assert xs ++ [] == xs;
}
*/
