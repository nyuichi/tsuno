use proc_macro::TokenStream;

use quote::quote;

#[proc_macro_attribute]
pub fn verify(_attr: TokenStream, _item: TokenStream) -> TokenStream {
    quote!(compile_error!("use `//@ verify` on the line immediately before the function");).into()
}
