#[repr(C)]
struct Padded {
    a: u8,
    b: u32,
    c: u8,
}

#[repr(C)]
struct Outer {
    tag: u8,
    inner: Padded,
}

fn repr_c_field_offsets() {
    let padded = Padded {
        a: 1u8,
        b: 2u32,
        c: 3u8,
    };
    let base = &raw const padded;
    let a = &raw const padded.a;
    let b = &raw const padded.b;
    let c = &raw const padded.c;

    //@ assert {a}.addr == {base}.addr;
    //@ assert {b}.addr == {base}.addr + 4usize;
    //@ assert {c}.addr == {base}.addr + 8usize;
    //@ assert {a}.prov == {base}.prov;
    //@ assert {b}.prov == {base}.prov;
    //@ assert {c}.prov == {base}.prov;
}

fn nested_field_offsets() {
    let outer = Outer {
        tag: 1u8,
        inner: Padded {
            a: 2u8,
            b: 3u32,
            c: 4u8,
        },
    };
    let base = &raw const outer;
    let tag = &raw const outer.tag;
    let inner = &raw const outer.inner;
    let inner_b = &raw const outer.inner.b;

    //@ assert {tag}.addr == {base}.addr;
    //@ assert {inner}.addr == {base}.addr + 4usize;
    //@ assert {inner_b}.addr == {base}.addr + 8usize;
    //@ assert {inner_b}.prov == {base}.prov;
}

fn deref_base_field_offsets() {
    let padded = Padded {
        a: 1u8,
        b: 2u32,
        c: 3u8,
    };
    let r = &padded;
    let base = &raw const padded;
    let b = &raw const (*r).b;

    //@ assert {b}.addr == {base}.addr + 4usize;
    //@ assert {b}.prov == {base}.prov;
}

fn main() {}
