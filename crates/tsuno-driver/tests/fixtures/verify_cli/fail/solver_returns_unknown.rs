//@ verify
fn solver_returns_unknown(x: i64, y: i64, z: i64) {
    if x >= -1_000_000
        && x <= 1_000_000
        && y >= -1_000_000
        && y <= 1_000_000
        && z >= -1_000_000
        && z <= 1_000_000
    {
        //@ assert "x * x * x + y * y * y + z * z * z != 42"
    }
}

fn main() {}
