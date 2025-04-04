use quote::quote;
use syn::Error;

use crate::internals::container::Container;
use crate::internals::context;

pub fn impl_derive(input: syn::DeriveInput) -> Result<proc_macro2::TokenStream, Vec<Error>> {
    let ctx = context::Ctxt::new();
    let container_opt = Container::from_ast(&ctx, &input);
    let Some(container) = container_opt else {
        return Err(ctx.check().unwrap_err());
    };
    let Some(tuple) = container.construct_into_abi(&ctx) else {
        return Err(ctx.check().unwrap_err());
    };

    let abi_values_slice = quote! {
        [ #(#tuple),* ]
    };

    let ident = container.name_ident;
    let (impl_generics, ty_generics, where_clause) = container.generics.split_for_impl();

    let token_stream = quote! {
        impl #impl_generics ::everscale_types::abi::IntoAbi for #ident #ty_generics #where_clause {
            #[inline]
            fn as_abi(&self) -> ::everscale_types::abi::AbiValue {
                ::everscale_types::abi::AbiValue::tuple(#abi_values_slice)
            }

            #[inline]
            fn into_abi(self) -> ::everscale_types::abi::AbiValue
            where
                Self: Sized,
            {
                self.as_abi()
            }
        }
    };

    Ok(token_stream)
}
