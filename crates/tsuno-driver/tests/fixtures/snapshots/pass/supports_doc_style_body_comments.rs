fn supports_doc_style_body_comments(x: i32) {
    //@ assert {x} == {x} &&
    /*@ true; */
    let y = x;

    /*@ assert {x} == {x}; */
    let z = y;

    /*@ assume {x} == {x}; */
    //@ assert {z} == {x};
}

fn main() {
    supports_doc_style_body_comments(1);
}
