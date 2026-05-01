use std::ptr;

struct Pair {
    a: u8,
    b: u8,
}

fn ptr_eq_u8(lhs: *const u8, rhs: *const u8) -> bool
//@ req true
//@ ens result == ({lhs}.addr == {rhs}.addr)
{
    //@ assume false;
    ptr::eq(lhs, rhs)
}

fn ptr_eq_mut_u8(lhs: *mut u8, rhs: *mut u8) -> bool
//@ req true
//@ ens result == ({lhs}.addr == {rhs}.addr)
{
    //@ assume false;
    ptr::eq(lhs, rhs)
}

fn null_u8() -> *const u8
//@ req true
//@ ens result.addr == 0usize && result.prov == Option::<Provenance>::None && result.ty == {type u8}
{
    //@ assume false;
    ptr::null::<u8>()
}

fn null_mut_u8() -> *mut u8
//@ req true
//@ ens result.addr == 0usize && result.prov == Option::<Provenance>::None && result.ty == {type u8}
{
    //@ assume false;
    ptr::null_mut::<u8>()
}

fn dangling_u8() -> *const u8
//@ req true
//@ ens result.addr != 0usize && result.prov == Option::<Provenance>::None && result.ty == {type u8}
{
    //@ assume false;
    ptr::dangling::<u8>()
}

fn addr_u8(ptr: *const u8) -> usize
//@ req true
//@ ens result == {ptr}.addr
{
    //@ assume false;
    ptr.addr()
}

fn with_addr_u8(ptr: *const u8, addr: usize) -> *const u8
//@ req true
//@ ens result.addr == {addr} && result.prov == {ptr}.prov && result.ty == {ptr}.ty
{
    //@ assume false;
    ptr.with_addr(addr)
}

fn pointer_identity_and_raw_borrows() {
    let x = 42u8;
    let y = 7u8;
    let r = &x;
    let p = &raw const x;
    let p_again = &raw const x;
    let q = &raw const y;
    let c = &x as *const u8;

    //@ assert {r}.ptr.addr == {p}.addr;
    //@ assert {r}.ptr.prov == {p}.prov;
    //@ assert {r}.ptr.ty == {type u8};
    //@ assert {p}.addr == {p_again}.addr;
    //@ assert {p}.prov == {p_again}.prov;
    //@ assert {p}.prov == Option::<Provenance>::Some(Provenance { base: {p}.addr });
    //@ assert {p}.prov != {q}.prov;
    //@ assert {p}.addr != {q}.addr;
    //@ assert {c}.addr == {p}.addr;
    //@ assert {c}.prov == {p}.prov;

    let pair = Pair { a: 1u8, b: 2u8 };
    let ppair = &raw const pair;
    let pa = &raw const pair.a;
    let pb = &raw const pair.b;
    //@ assert {pa}.prov == {pb}.prov;
    //@ assert {pa}.addr != {pb}.addr;
    //@ assert {pa}.prov == Option::<Provenance>::Some(Provenance { base: {ppair}.addr });
    //@ assert {pa}.ty == {type u8};

    let mut z = 11u8;
    let pm = &raw mut z;
    //@ assert {pm}.ty == {type u8};
    //@ assert {pm}.prov != Option::<Provenance>::None;
}

fn strict_provenance_and_ptr_apis() {
    let x = 42u8;
    let p = &raw const x;
    let same = &raw const x;
    let n = null_u8();
    let nm = null_mut_u8();
    let d = dangling_u8();
    let p_addr = addr_u8(p);
    let d_addr = addr_u8(d);
    let moved = with_addr_u8(p, d_addr);
    let eq_same = ptr_eq_u8(p, same);
    let eq_mut_null = ptr_eq_mut_u8(nm, nm);
    let eq_null = ptr_eq_u8(p, n);
    let eq_null_dangling = ptr_eq_u8(n, d);

    //@ assert {p}.addr == {p_addr};
    //@ assert {moved}.addr == {d}.addr;
    //@ assert {moved}.prov == {p}.prov;
    //@ assert {moved}.ty == {type u8};
    //@ assert {eq_same} == true;
    //@ assert {eq_null} == false;
    //@ assert {eq_null_dangling} == false;
    //@ assert {n}.addr == 0usize;
    //@ assert {n}.prov == Option::<Provenance>::None;
    //@ assert {n}.ty == {type u8};
    //@ assert {nm}.addr == 0usize;
    //@ assert {nm}.prov == Option::<Provenance>::None;
    //@ assert {nm}.ty == {type u8};
    //@ assert {eq_mut_null} == true;
    //@ assert {d}.addr != 0usize;
    //@ assert {d}.prov == Option::<Provenance>::None;
    //@ assert {d}.ty == {type u8};
}

fn integer_to_pointer_casts() {
    let p = 0x1234 as *const u8;
    let pm = 0x5678usize as *mut u8;
    let zero = 0usize as *const u8;

    //@ assert {p}.addr == 4660usize;
    //@ assert {p}.prov == Option::<Provenance>::None;
    //@ assert {p}.ty == {type u8};
    //@ assert {pm}.addr == 22136usize;
    //@ assert {pm}.prov == Option::<Provenance>::None;
    //@ assert {pm}.ty == {type u8};
    //@ assert {zero}.addr == 0usize;
    //@ assert {zero}.prov == Option::<Provenance>::None;
    //@ assert {zero}.ty == {type u8};
}

fn main() {}
