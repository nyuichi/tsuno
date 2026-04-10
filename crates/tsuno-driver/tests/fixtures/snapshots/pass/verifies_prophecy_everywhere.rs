fn mut_ref_model_everywhere(mut x: i32) {
    {
        let r = &mut x;
        while *r < 1
          //@ inv "{r}.cur == {r}.cur && {r}.fin == {r}.fin"
        {
            break;
        }
    }
    let s = &mut x;
    //@ assert "{s}.cur == {s}.cur && {s}.fin == {s}.fin"
    let _sink = helper(s);
}

//@ req "{x}.cur == {x}.cur && {x}.fin == {x}.fin"
//@ ens "{x}.cur == {x}.cur && {x}.fin == {x}.fin"
fn helper(x: &mut i32) -> i32 {
    *x
}

fn main() {}
