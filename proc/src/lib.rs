use proc_macro::TokenStream;
use quote::quote;

mod bound;
mod derive_clone;
mod derive_debug;
mod internals;

#[derive(Copy, Clone, Eq, PartialEq)]
enum Derive {
    Debug,
}

/// Implements [`Clone`] for the type.
///
/// [`Clone`]: std::fmt::Clone
#[proc_macro_derive(CustomClone, attributes(bounds))]
pub fn derive_clone(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_clone::impl_derive_clone(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

/// Implements [`Debug`] for the type.
///
/// [`Debug`]: std::fmt::Debug
#[proc_macro_derive(CustomDebug, attributes(debug, bounds))]
pub fn derive_debug(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_debug::impl_derive_debug(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

fn to_compile_errors(errors: Vec<syn::Error>) -> proc_macro2::TokenStream {
    let compile_errors = errors.iter().map(syn::Error::to_compile_error);
    quote!(#(#compile_errors)*)
}
