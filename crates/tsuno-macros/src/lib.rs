use proc_macro::TokenStream;

use quote::quote;
use syn::{Expr, ExprLoop, ItemFn, parse_macro_input, parse_quote};

#[proc_macro_attribute]
pub fn verify(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut item_fn = parse_macro_input!(item as ItemFn);
    item_fn
        .block
        .stmts
        .insert(0, parse_quote!(::tsuno::__tsuno_verify();));
    quote!(#item_fn).into()
}

#[proc_macro_attribute]
pub fn invariant(attr: TokenStream, item: TokenStream) -> TokenStream {
    let invariant_expr = parse_macro_input!(attr as Expr);
    let mut loop_expr = parse_macro_input!(item as ExprLoop);
    let marker_stmt = parse_quote! {
        ::tsuno::__tsuno_invariant(#invariant_expr);
    };
    loop_expr.body.stmts.insert(0, marker_stmt);
    quote!(#loop_expr).into()
}
