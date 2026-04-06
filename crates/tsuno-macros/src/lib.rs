use proc_macro::TokenStream;

use quote::quote;
use syn::{Expr, ItemFn, LitStr, parse_macro_input, parse_quote};

#[proc_macro_attribute]
pub fn verify(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut item_fn = parse_macro_input!(item as ItemFn);
    item_fn
        .block
        .stmts
        .insert(0, parse_quote!(::tsuno::__tsuno_verify();));
    quote!(#item_fn).into()
}

#[proc_macro]
pub fn inv(input: TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);
    let expr = match parse_inv_input(input.clone()) {
        Ok(expr) => expr,
        Err(err) => return err.to_compile_error().into(),
    };
    quote! {{
        ::tsuno::__tsuno_invariant(#expr);
    }}
    .into()
}

fn parse_inv_input(input: proc_macro2::TokenStream) -> syn::Result<Expr> {
    if let Ok(lit) = syn::parse2::<LitStr>(input.clone()) {
        return parse_inv_template(&lit);
    }
    syn::parse2::<Expr>(input)
}

fn parse_inv_template(lit: &LitStr) -> syn::Result<Expr> {
    let raw = lit.value();
    let mut output = String::new();
    let mut rest = raw.as_str();
    while let Some(start) = rest.find('{') {
        if rest[start..].starts_with("{{") {
            output.push_str(&rest[..start]);
            output.push('{');
            rest = &rest[start + 2..];
            continue;
        }

        output.push_str(&rest[..start]);
        let after = &rest[start + 1..];
        let Some(end) = after.find('}') else {
            return Err(syn::Error::new(
                lit.span(),
                "unclosed `{` in tsuno::inv! template",
            ));
        };
        let inner = after[..end].trim();
        if inner.is_empty() {
            return Err(syn::Error::new(
                lit.span(),
                "empty interpolation in tsuno::inv! template",
            ));
        }
        output.push('(');
        output.push_str(inner);
        output.push(')');
        rest = &after[end + 1..];
    }
    output.push_str(&rest.replace("}}", "}").replace("{{", "{"));
    syn::parse_str::<Expr>(&output).map_err(|err| {
        syn::Error::new(
            lit.span(),
            format!("failed to parse tsuno::inv! predicate: {err}"),
        )
    })
}
