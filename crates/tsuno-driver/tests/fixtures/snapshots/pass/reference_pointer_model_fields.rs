/*@
fn ref_model_value(r: Ref<i32>) -> i32 {
    *r
}

fn mut_model_value(r: Mut<i32>) -> i32 {
    *r
}
*/

fn reference_pointer_model_fields(x: &i32, p: *const i32) {
    //@ assert ref_model_value({x}) == *{x};
    //@ assert {x}.deref == *{x};
    //@ assert {x}.ptr.ty == {type i32};
    //@ assert {x}.ptr.prov != Option::<Provenance>::None;
    //@ assert {p}.ty == {type i32};
    //@ assert {type i32} != {type u32};
    //@ assert {p}.addr == {p}.addr;
    //@ assert {p}.prov == {p}.prov;
}

fn generic_pointer_model_field<T>(p: *const T) {
    //@ assert {p}.ty == {type T};
}

fn main() {}
