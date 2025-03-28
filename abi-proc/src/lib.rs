mod common;
mod derive_from_abi;
mod derive_into_abi;
mod derive_with_abi_type;

use proc_macro::TokenStream;

#[proc_macro_derive(IntoAbi, attributes(abi))]
pub fn derive_into_abi(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_into_abi::impl_derive(input)
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

#[proc_macro_derive(WithAbiType, attributes(abi))]
pub fn derive_with_abi_type(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_with_abi_type::impl_derive(input)
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}

#[proc_macro_derive(FromAbi, attributes(abi))]
pub fn derive_from_abi(input: TokenStream) -> TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    derive_from_abi::impl_derive(input)
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}
