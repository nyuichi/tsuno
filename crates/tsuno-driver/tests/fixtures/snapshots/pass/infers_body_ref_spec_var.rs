fn main() {
    let x = 1;
    let r = &x;
    //@ assert ?V == *{r};
    //@ assert V == *{r};
}
