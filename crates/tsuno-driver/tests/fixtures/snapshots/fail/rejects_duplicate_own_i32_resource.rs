/*@
unsafe lem make_own_i32(v: i32)
  raw req emp
  raw ens Own::<i32>(v)
{
    assume false;
}
*/

unsafe fn rejects_duplicate_own_i32_resource() {
    unsafe {
        //@ make_own_i32(1i32);
        //@ raw assert Own::<i32>(1i32) * Own::<i32>(1i32);
    }
}

fn main() {}
