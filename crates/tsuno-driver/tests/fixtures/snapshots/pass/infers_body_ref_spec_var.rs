fn main() {
    let x = 1;
    let r = &x;
    //@ assert "?V == *{r}"
    let _ = ();
    //@ assert "V == *{r}"
    let _ = ();
}
