use crate::common;
use crate::common::{FieldAttributes, HandlerType};
use quote::quote;
use syn::Error;

pub fn impl_derive(input: syn::DeriveInput) -> Result<proc_macro2::TokenStream, Error> {
    let data = match &input.data {
        syn::Data::Struct(data_struct) => data_struct,
        syn::Data::Enum(_) => {
            return Err(Error::new_spanned(
                &input,
                "FromAbi is not supported for enum",
            ))
        }
        syn::Data::Union(_) => {
            return Err(Error::new_spanned(
                &input,
                "FromAbi is not supported for unions",
            ))
        }
    };

    let mut struct_fields = Vec::new();

    let ident = &input.ident;

    for i in &data.fields {
        let Some(name) = &i.ident else {
            continue;
        };

        let attributes = common::extract_field_attributes(i.attrs.as_slice())?;
        let token = construct_from_abi(name, &attributes)?;
        struct_fields.push(token);
    }

    let token_stream = quote! {
        impl ::everscale_types::abi::FromAbi for #ident {
            fn from_abi(value: ::everscale_types::abi::AbiValue) -> anyhow::Result<Self> {
                let ::everscale_types::abi::AbiValue::Tuple(inner) = value else {
                    anyhow::bail!("AbiValue has incorrect type")
                };
                let mut iter = inner.iter();
                Ok(Self { #(#struct_fields),* })
            }
        }
    };

    Ok(token_stream)
}

pub fn construct_from_abi(
    field_name: &syn::Ident,
    attrs: &FieldAttributes,
) -> Result<proc_macro2::TokenStream, Error> {
    attrs.check()?;

    for (ty, path) in &attrs.with_handlers {
        if !matches!(ty, HandlerType::FromAbi) {
            continue;
        }

        return Ok(quote! {
            #field_name: #path(
                iter.next()
                .ok_or(anyhow::anyhow!("unable to get field from abi"))?.value.clone())?
        });
    }

    //fallback to mod handler if present
    Ok(match &attrs.mod_handler {
        Some(path) => {
            quote! {
                #field_name: #path::from_abi(
                    iter.next()
                    .ok_or(anyhow::anyhow!("unable to get field from abi"))?.value.clone())?
            }
        }
        None => {
            quote!(#field_name: <_>::from_abi(
                iter.next()
                .ok_or(anyhow::anyhow!("unable to get field from abi"))?.value.clone())?
            )
        }
    })
}
