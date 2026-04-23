fn req_binder_is_visible_in_body(x: i32)
//@ req ?V == {x}
//@ ens true
{
    //@ assert V == {x};
}

fn main() {
    req_binder_is_visible_in_body(1);
}
