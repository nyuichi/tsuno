fn assumes_false_prunes_following_assertion() {
    //@ assume "false"
    let _x: [i32; 3] = [1_i32, 2_i32, 3_i32];
    //@ assert "1 + 1 == 3"
}

fn main() {}
