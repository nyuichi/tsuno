/*@
unsafe fn keep_i32_cell(p: Ptr)
  req p.prov == Option::Some(Provenance { base: p.addr })
  resource req PointsTo(p.addr, {type i32}, Option::Some(?old)) * Alloc(p.addr, 4usize, 4usize)
  resource ens PointsTo(p.addr, {type i32}, Option::Some(?v)) * Alloc(p.addr, 4usize, 4usize) where v == old
{
}
*/

unsafe fn unsafe_lemma_resource_contract() {
    let mut x = 42i32;
    let p = &raw mut x;
    //@ keep_i32_cell({p});
    //@ resource assert *p |-> Option::Some(?v) where v == 42i32;
    //@ assert v == 42i32;
    let _keep = p;
}

fn main() {
    unsafe {
        unsafe_lemma_resource_contract();
    }
}
