//@ verify
fn reads_shared_reborrow_from_mut_ref(mut x: i32) {
    let m = &mut x;
    *m = 2;
    {
        let s = &*m;
        let y = *s;
        //@ assert "{y} == 2"
    }
    *m = 3;
}

fn main() {}
