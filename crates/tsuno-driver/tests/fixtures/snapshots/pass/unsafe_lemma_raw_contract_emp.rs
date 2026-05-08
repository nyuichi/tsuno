/*@
unsafe lem empty_unsafe_lemma()
  raw req emp
  raw ens emp
{
}

unsafe lem keep_i32_cell_with_emp(p: Ptr)
  raw req emp * PointsTo(p.addr, {type i32}, Option::Some(?old))
  raw ens PointsTo(p.addr, {type i32}, Option::Some(?v)) * emp where v == old
{
}
*/

unsafe fn unsafe_lemma_raw_contract_emp() {
    let mut x = 42i32;
    let p = &raw mut x;
    //@ empty_unsafe_lemma();
    //@ keep_i32_cell_with_emp({p});
    //@ raw assert *p |-?-> Option::Some(?v) where v == 42i32;
    //@ assert v == 42i32;
    let _keep = p;
}

fn main() {
    unsafe {
        unsafe_lemma_raw_contract_emp();
    }
}
