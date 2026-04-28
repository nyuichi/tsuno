#[repr(align(16))]
struct Aligned(u8);

fn aligned_local_pointer_addr() {
    let value = Aligned(1u8);
    let ptr = &raw const value;

    //@ assert {ptr}.addr != 1usize;
}

fn main() {}
