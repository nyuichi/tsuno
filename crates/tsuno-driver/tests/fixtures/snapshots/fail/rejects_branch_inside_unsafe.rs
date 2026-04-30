fn rejects_branch_inside_unsafe(flag: bool) {
    let mut x = 1i32;

    unsafe {
        if flag {
            x = 2i32;
        }
    }
}

fn main() {}
