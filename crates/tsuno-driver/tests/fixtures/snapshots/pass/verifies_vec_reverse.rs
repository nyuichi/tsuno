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
    let mut acc = vec_new();
    //@ assert seq_rev(Input) == {acc} ++ seq_rev({xs});
    while !vec_is_empty(&xs)
    //@ inv seq_rev(Input) == {acc} ++ seq_rev({xs})
    {
        let x = vec_pop(&mut xs);
        //@ assert seq_rev(Input) == {acc} ++ ([{x}] ++ seq_rev({xs}));
        //@ seq_concat_assoc({acc}, [{x}], seq_rev({xs}));
        vec_push(&mut acc, x);
        //@ assert seq_rev(Input) == {acc} ++ seq_rev({xs});
    }
    //@ seq_rev_empty({xs});
    //@ seq_concat_empty_right({acc});
    acc
}

fn main() {}
