//@ verify
fn caller() {
    sink(1_i32);
}

fn sink(x: i32) {
    let _ = x;
}

fn main() {}
