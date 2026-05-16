unsafe fn preserves_i32_own(p: *mut i32)
//@ raw req *p |-?-> Option::<i32>::Some(?v) * Own::<i32>(v);
//@ raw ens *p |-?-> Option::<i32>::Some(v) * Own::<i32>(v);
{
    unsafe {
        //@ raw assert *p |-?-> Option::<i32>::Some(?w) * Own::<i32>(w);
    }
}

fn main() {}
