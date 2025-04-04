use quote::quote;

use crate::internals::container::Container;
use crate::internals::context;

pub fn impl_derive(input: syn::DeriveInput) -> Result<proc_macro2::TokenStream, Vec<syn::Error>> {
    let ctx = context::Ctxt::new();
    let Some(container) = Container::from_ast(&ctx, &input) else {
        return Err(ctx.check().unwrap_err());
    };

    let Some(tuple) = container.construct_with_abi_type(&ctx) else {
        return Err(ctx.check().unwrap_err());
    };

    let ident = &input.ident;
    let (impl_generics, ty_generics, where_clause) = container.generics.split_for_impl();

    let abi_values_slice = quote! {
        [ #(#tuple),* ]
    };

    let token_stream = quote! {
        impl #impl_generics ::everscale_types::abi::WithAbiType for #ident #ty_generics #where_clause {
            fn abi_type() -> ::everscale_types::abi::AbiType {
                ::everscale_types::abi::AbiType::tuple(#abi_values_slice)
            }
        }
    };

    Ok(token_stream)
}
