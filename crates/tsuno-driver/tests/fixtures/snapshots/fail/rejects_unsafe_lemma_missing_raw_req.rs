/*@
unsafe fn needs_i32_cell(p: Ptr)
  raw req PointsTo(p.addr, {type i32}, Option::Some(?old)) where old == 0i32
  raw ens PointsTo(p.addr, {type i32}, Option::Some(?v)) where v == old
{
}
*/

fn rejects_unsafe_lemma_missing_raw_req() {
    let mut x = 42i32;
    let p = &raw mut x;
    unsafe {
        //@ needs_i32_cell({p});
        let _keep = p;
    }
}

fn main() {}
