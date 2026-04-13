#[derive(Copy, Clone)]
struct Pair {
    left: i32,
    right: bool,
}

fn supports_struct_field_access_in_contract(pair: Pair)
//@ req "{pair}.left == 1i32"
//@ ens "{pair}.right == false"
{}

fn main() {
    supports_struct_field_access_in_contract(Pair {
        left: 1,
        right: false,
    });
}
