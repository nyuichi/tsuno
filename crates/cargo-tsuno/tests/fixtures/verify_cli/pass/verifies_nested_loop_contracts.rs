#[tsuno::verify]
fn nested_loops(mut x: i32) {
    let limit = 3_i32;
    while x < limit {
        tsuno::inv!("0 <= {x} && {x} <= {limit}");
        let mut y = 0_i32;
        while y < x {
            tsuno::inv!("0 <= {y} && {y} <= {x}");
            break;
        }
        x = x + 1;
    }
}

fn main() {}
