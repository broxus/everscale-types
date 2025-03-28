use crate::common;
use crate::common::{FieldAttributes, HandlerType};
use quote::quote;
use syn::Error;

pub fn impl_derive(input: syn::DeriveInput) -> Result<proc_macro2::TokenStream, Error> {
    let data = match input.data {
        syn::Data::Struct(data_struct) => data_struct,
        syn::Data::Enum(_) => {
            return Err(Error::new_spanned(
                &input,
                "IntoAbi is not supported for enum",
            ))
        }
        syn::Data::Union(_) => {
            return Err(Error::new_spanned(
                &input,
                "IntoAbi is not supported for unions",
            ))
        }
    };

    let ident = &input.ident;

    let mut tuple = Vec::new();

    for i in data.fields {
        let Some(name) = &i.ident else {
            continue;
        };

        let attributes = common::extract_field_attributes(i.attrs.as_slice())?;
        let token = construct_named_abi_value(name, &attributes)?;

        tuple.push(token);
    }

    let abi_values_slice = quote! {
        [ #(#tuple),* ]
    };

    let token_stream = quote! {
        impl ::everscale_types::abi::IntoAbi for #ident {
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

pub fn construct_named_abi_value(
    field_name: &syn::Ident,
    attrs: &FieldAttributes,
) -> Result<proc_macro2::TokenStream, Error> {
    attrs.check()?;

    let to_change = match &attrs.custom_name {
        Some(custom) => custom.to_string(),
        None => field_name.to_string(),
    };
    let custom_name = to_change.to_string();

    for (ty, path) in &attrs.with_handlers {
        if !matches!(ty, HandlerType::IntoAbi) {
            continue;
        }

        return Ok(quote! {
            quote!(#path(self.#field_name.clone()).named(#custom_name))
        });
    }

    //fallback to mod handler if present
    Ok(match &attrs.mod_handler {
        Some(handler) => quote!(#handler::into_abi(self.#field_name.clone()).named(#custom_name)),
        None => quote!(self.#field_name.clone().into_abi().named(#custom_name)),
    })
}
