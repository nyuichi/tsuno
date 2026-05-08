/*@
unsafe extern fn legacy_replace_i32(ptr: *mut i32, value: i32) -> i32
  raw req *ptr |-?-> Option::<i32>::Some(?old)
  raw ens *ptr |-?-> Option::<i32>::Some(value)
  ens result == old
;
*/

fn main() {}
