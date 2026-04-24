//@ fn line_comment_lemma(n: Nat)
//@   req true
//@   ens true
//@ {}

/*@ fn mixed_comment_lemma(n: Nat) */
//@   req true
/*@   ens true */
//@ {}

fn supports_line_comment_ghost_items() {
    //@ line_comment_lemma(Nat::Zero);
    //@ mixed_comment_lemma(Nat::Succ(Nat::Zero));
}

fn supports_block_loop_invariant() {
    let mut x = 0;
    while x < 3
      /*@ inv 0 <= {x} && {x} <= 3 */
    {
        x = x + 1;
    }
}

fn main() {
    supports_line_comment_ghost_items();
    supports_block_loop_invariant();
}
