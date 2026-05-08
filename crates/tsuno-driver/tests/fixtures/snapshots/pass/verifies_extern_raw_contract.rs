/*@
unsafe extern fn external_replace_i32(ptr: *mut i32, value: i32) -> i32
  raw req *ptr |-?-> Option::<i32>::Some(?old)
  raw ens *ptr |-?-> Option::<i32>::Some(value)
  ens result == old
;
*/

unsafe extern "Rust" {
    fn external_replace_i32(ptr: *mut i32, value: i32) -> i32;
}

unsafe fn caller(p: *mut i32, value: i32) -> i32
//@ raw req *p |-?-> Option::Some(?old);
//@ raw ens *p |-?-> Option::Some(?new) where new == {value};
//@ ens result == old
{
    unsafe { external_replace_i32(p, value) }
}

fn main() {}
