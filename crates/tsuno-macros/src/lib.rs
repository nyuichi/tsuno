use proc_macro::TokenStream;

use quote::quote;
use syn::{ItemFn, parse_macro_input, parse_quote};

#[proc_macro_attribute]
pub fn verify(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut item_fn = parse_macro_input!(item as ItemFn);
    item_fn
        .block
        .stmts
        .insert(0, parse_quote!(::tsuno::__tsuno_verify();));
    quote!(#item_fn).into()
}
