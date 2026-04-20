/*@
fn bad_assume(x: i64, y: i64, z: i64)
  req x >= -1000000i64 && x <= 1000000i64 && y >= -1000000i64 && y <= 1000000i64 && z >= -1000000i64 && z <= 1000000i64
  ens true
{
    assume x * x * x + y * y * y + z * z * z == 42i64;
}
*/

fn main() {}
