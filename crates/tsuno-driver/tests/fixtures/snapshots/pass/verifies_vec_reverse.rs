/*@
fn is_rev(x: Seq<i32>, y: Seq<i32>) -> bool {
    seq_rev(x) == y
}

fn rev_state(orig: Seq<i32>, i: usize) -> Seq<i32> {
    seq_concat(seq_concat(seq_rev(seq_extract(orig, seq_len(orig) - i, i)), seq_extract(orig, i, seq_len(orig) - i - i)), seq_rev(seq_extract(orig, 0usize, i)))
}

fn rev_inv(orig: Seq<i32>, cur: Seq<i32>, i: usize) -> bool {
    cur == rev_state(orig, i) && i + i <= seq_len(orig) && (seq_len(orig) > i + i + 1usize || is_rev(orig, cur))
}

fn unit_rev(x: i32)
  req true
  ens seq_rev(seq_unit(x)) == seq_unit(x)
{
    assert seq_rev(seq_unit(x)) == seq_unit(x);
}

fn rev_step(orig: Seq<i32>, i: usize)
  req i + i + 1usize < seq_len(orig)
  ens seq_concat(seq_concat(seq_concat(seq_rev(seq_extract(orig, seq_len(orig) - i, i)), seq_unit(seq_nth(orig, seq_len(orig) - i - 1usize))), seq_concat(seq_extract(orig, i + 1usize, seq_len(orig) - i - i - 2usize), seq_unit(seq_nth(orig, i)))), seq_rev(seq_extract(orig, 0usize, i))) == rev_state(orig, i + 1usize)
{
    assert seq_extract(orig, seq_len(orig) - i - 1usize, i + 1usize) == seq_concat(seq_unit(seq_nth(orig, seq_len(orig) - i - 1usize)), seq_extract(orig, seq_len(orig) - i, i));
    unit_rev(seq_nth(orig, seq_len(orig) - i - 1usize));
    assert seq_rev(seq_extract(orig, seq_len(orig) - i - 1usize, i + 1usize)) == seq_concat(seq_rev(seq_extract(orig, seq_len(orig) - i, i)), seq_unit(seq_nth(orig, seq_len(orig) - i - 1usize)));
    assert seq_extract(orig, 0usize, i + 1usize) == seq_concat(seq_extract(orig, 0usize, i), seq_unit(seq_nth(orig, i)));
    unit_rev(seq_nth(orig, i));
    assert seq_rev(seq_extract(orig, 0usize, i + 1usize)) == seq_concat(seq_unit(seq_nth(orig, i)), seq_rev(seq_extract(orig, 0usize, i)));
    assert rev_state(orig, i + 1usize) == seq_concat(seq_concat(seq_concat(seq_rev(seq_extract(orig, seq_len(orig) - i, i)), seq_unit(seq_nth(orig, seq_len(orig) - i - 1usize))), seq_concat(seq_extract(orig, i + 1usize, seq_len(orig) - i - i - 2usize), seq_unit(seq_nth(orig, i)))), seq_rev(seq_extract(orig, 0usize, i)));
}
*/

// TODO: Define seq_extract and seq_rev in spec code once recursive pure functions are supported.
// For now they remain built-ins.

fn vec_len(v: &Vec<i32>) -> usize
//@ req true
//@ ens {result} == seq_len(*{v})
{
    //@ assume false;
    return v.len();
}

fn vec_swap(v: &mut Vec<i32>, i: usize, j: usize)
//@ req ?old == *{v} && {i} < {j} && {j} < seq_len(old)
//@ ens {v}.fin == seq_concat(seq_concat(seq_concat(seq_extract(old, 0usize, {i}), seq_unit(seq_nth(old, {j}))), seq_concat(seq_extract(old, {i} + 1usize, {j} - {i} - 1usize), seq_unit(seq_nth(old, {i})))), seq_extract(old, {j} + 1usize, seq_len(old) - {j} - 1usize))
{
    //@ assume false;
    v.swap(i, j);
}

fn rev(v: &mut Vec<i32>)
//@ req ?orig == *{v}
//@ ens is_rev(orig, {v}.fin)
{
    let n = vec_len(v);
    let mut i = 0usize;
    //@ assert {n} == seq_len(orig) && rev_inv(orig, *{v}, 0usize);
    while i + i + 1usize < n
      //@ inv {n} == seq_len(orig) && rev_inv(orig, *{v}, {i})
    {
        let j = n - i - 1usize;
        vec_swap(v, i, j);
        //@ assert *{v} == seq_concat(seq_concat(seq_concat(seq_rev(seq_extract(orig, seq_len(orig) - {i}, {i})), seq_unit(seq_nth(orig, seq_len(orig) - {i} - 1usize))), seq_concat(seq_extract(orig, {i} + 1usize, seq_len(orig) - {i} - {i} - 2usize), seq_unit(seq_nth(orig, {i})))), seq_rev(seq_extract(orig, 0usize, {i})));
        //@ rev_step(orig, {i});
        i = i + 1usize;
        //@ assert rev_inv(orig, *{v}, {i});
    }
    //@ assert {n} <= {i} + {i} + 1usize;
    //@ assert rev_inv(orig, *{v}, {i});
    //@ assert is_rev(orig, *{v});
}

fn main() {}
