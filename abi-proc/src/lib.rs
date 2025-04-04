mod derive_from_abi;
mod derive_into_abi;
mod derive_with_abi_type;
mod internals;

use proc_macro::TokenStream;
use quote::quote;

#[proc_macro_derive(IntoAbi, attributes(abi))]
pub fn derive_into_abi(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_into_abi::impl_derive(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

#[proc_macro_derive(WithAbiType, attributes(abi))]
pub fn derive_with_abi_type(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_with_abi_type::impl_derive(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

#[proc_macro_derive(FromAbi, attributes(abi))]
pub fn derive_from_abi(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_from_abi::impl_derive(input)
        .unwrap_or_else(to_compile_errors)
        .into()
}

fn to_compile_errors(errors: Vec<syn::Error>) -> proc_macro2::TokenStream {
    let compile_errors = errors.iter().map(syn::Error::to_compile_error);
    quote!(#(#compile_errors)*)
}
