/*@
fn raw_safe(ptr: *mut i32) -> i32
  raw req *ptr |-?-> Option::<i32>::Some(?old)
  ens result == old
;
*/

fn main() {}
