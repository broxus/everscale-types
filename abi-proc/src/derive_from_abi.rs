use crate::internals::container::Container;
use crate::internals::context::Ctxt;
use quote::quote;
use syn::Error;

pub fn impl_derive(input: syn::DeriveInput) -> Result<proc_macro2::TokenStream, Vec<Error>> {
    let ctx = Ctxt::new();
    let container_opt = Container::from_ast(&ctx, &input);

    let Some(container) = container_opt else {
        return Err(ctx.check().unwrap_err());
    };

    let Some(struct_fields) = container.construct_from_abi(&ctx) else {
        return Err(ctx.check().unwrap_err());
    };

    let ident = container.name_ident;
    let (impl_generics, ty_generics, where_clause) = container.generics.split_for_impl();

    let token_stream = quote! {
        impl #impl_generics ::everscale_types::abi::FromAbi for #ident #ty_generics #where_clause {
            fn from_abi(value: ::everscale_types::abi::AbiValue) -> everscale_types::abi::__export::anyhow::Result<Self> {
                let ::everscale_types::abi::AbiValue::Tuple(inner) = value else {
                     everscale_types::abi::__export::anyhow::bail!("AbiValue has incorrect type")
                };
                let mut iter = inner.iter();
                Ok(Self { #(#struct_fields),* })
            }
        }
    };

    Ok(token_stream)
}
