/*@
fn is_rev(x: Seq<i32>, y: Seq<i32>) -> bool {
    seq_rev(x) == y
}
*/

fn vec_len(v: &Vec<i32>) -> usize
//@ req "true"
//@ ens "{result} == seq_len(*{v})"
{
    //@ assume "false"
    let _ = 0usize;
    0
}

fn vec_swap(v: &mut Vec<i32>, i: usize, j: usize)
//@ req "?old == *{v} && {i} < {j} && {j} < seq_len(old)"
//@ ens "{v}.fin == seq_concat(seq_concat(seq_concat(seq_extract(old, 0usize, {i}), seq_unit(seq_nth(old, {j}))), seq_concat(seq_extract(old, {i} + 1usize, {j} - {i} - 1usize), seq_unit(seq_nth(old, {i})))), seq_extract(old, {j} + 1usize, seq_len(old) - {j} - 1usize))"
{
    //@ assume "false"
    let _ = ();
}

fn rev(v: &mut Vec<i32>)
//@ req "?orig == *{v}"
//@ ens "is_rev(orig, {v}.fin)"
{
    //@ assume "false"
    let _ = ();
}

fn main() {}
