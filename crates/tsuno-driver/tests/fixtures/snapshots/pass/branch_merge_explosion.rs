fn branch_merge_explosion(
    b0: bool,
    b1: bool,
    b2: bool,
    b3: bool,
    b4: bool,
    b5: bool,
    b6: bool,
    b7: bool,
    b8: bool,
    b9: bool,
    b10: bool,
    b11: bool,
) {
    let mut value = 0i32;
    if b0 {
        value += 1;
    } else {
        value += 2;
    }
    if b1 {
        value += 1;
    } else {
        value += 2;
    }
    if b2 {
        value += 1;
    } else {
        value += 2;
    }
    if b3 {
        value += 1;
    } else {
        value += 2;
    }
    if b4 {
        value += 1;
    } else {
        value += 2;
    }
    if b5 {
        value += 1;
    } else {
        value += 2;
    }
    if b6 {
        value += 1;
    } else {
        value += 2;
    }
    if b7 {
        value += 1;
    } else {
        value += 2;
    }
    if b8 {
        value += 1;
    } else {
        value += 2;
    }
    if b9 {
        value += 1;
    } else {
        value += 2;
    }
    if b10 {
        value += 1;
    } else {
        value += 2;
    }
    if b11 {
        value += 1;
    } else {
        value += 2;
    }
    //@ assert "{value} >= 0"
}

fn main() {}
