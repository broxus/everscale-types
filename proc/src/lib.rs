use proc_macro::TokenStream;
use quote::quote;

mod bound;
mod derive_clone;
mod derive_debug;
mod derive_eq;
mod derive_load;
mod derive_store;
mod internals;

#[derive(Copy, Clone, Eq, PartialEq)]
enum Derive {
    Debug,
}

/// Implements [`Clone`] for the type.
#[proc_macro_derive(CustomClone, attributes(bounds))]
pub fn derive_clone(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_clone::impl_derive(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

/// Implements [`Debug`] for the type.
///
/// [`Debug`]: core::fmt::Debug
#[proc_macro_derive(CustomDebug, attributes(debug, bounds))]
pub fn derive_debug(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_debug::impl_derive(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

/// Implements [`Eq`] and [`PartialEq`] for the type.
#[proc_macro_derive(CustomEq, attributes(bounds))]
pub fn derive_eq(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_eq::impl_derive(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

/// Implements `Load` for the type.
#[proc_macro_derive(Load, attributes(bounds, tlb))]
pub fn derive_load(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_load::impl_derive(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

/// Implements `Store` for the type.
#[proc_macro_derive(Store, attributes(bounds, tlb))]
pub fn derive_store(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_store::impl_derive(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

fn to_compile_errors(errors: Vec<syn::Error>) -> proc_macro2::TokenStream {
    let compile_errors = errors.iter().map(syn::Error::to_compile_error);
    quote!(#(#compile_errors)*)
}
