//@ req "true"
//@ ens "?R == result && result == x"
fn id(x: i32) -> i32 {
    x
}

fn rejects_equal_results_from_distinct_contract_binders() {
    let a = id(1);
    let b = id(2);
    //@ assert "{a} == {b}"
}

fn main() {
    rejects_equal_results_from_distinct_contract_binders();
}
