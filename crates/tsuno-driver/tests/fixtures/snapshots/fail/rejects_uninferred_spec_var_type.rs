//@ req "?X == ?Y"
//@ ens "true"
fn rejects_uninferred_spec_var_type() {}

fn main() {
    rejects_uninferred_spec_var_type();
}
