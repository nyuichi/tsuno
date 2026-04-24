fn rejects_legacy_question_binding(x: i32)
//@ req ?y == {x}
//@ ens true
{
}

fn main() {
    rejects_legacy_question_binding(1);
}
