fn vec_new() -> Vec<i32>
//@ req true
//@ ens {result} == []
{
    //@ assume false;
    Vec::new()
}

fn vec_is_empty(xs: &Vec<i32>) -> bool
//@ req true
//@ ens {result} == (*{xs} == [])
{
    //@ assume false;
    xs.is_empty()
}

fn vec_push(xs: &mut Vec<i32>, x: i32)
//@ req ?Old == *{xs}
//@ ens {xs}.fin == Old ++ [{x}]
{
    //@ assume false;
    xs.push(x);
}

fn vec_pop(xs: &mut Vec<i32>) -> i32
//@ req ?Old == *{xs} && !(Old == [])
//@ ens {xs}.fin ++ [{result}] == Old && seq_rev(Old) == [{result}] ++ seq_rev({xs}.fin)
{
    //@ assume false;
    xs.pop().unwrap()
}

fn reverse(mut xs: Vec<i32>) -> Vec<i32>
//@ req ?Input == {xs}
//@ ens {result} == seq_rev(Input)
{
    //@ assume false;
    xs
}

fn main() {}
