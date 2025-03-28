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
                "WithAbiType is not supported for enum",
            ))
        }
        syn::Data::Union(_) => {
            return Err(Error::new_spanned(
                &input,
                "WithAbiType is not supported for unions",
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
        let token = construct_with_abi_type(name, &i.ty, attributes)?;

        tuple.push(token);
    }

    let abi_values_slice = quote! {
        [ #(#tuple),* ]
    };

    let token_stream = quote! {
        impl ::everscale_types::abi::WithAbiType for #ident {
            fn abi_type() -> ::everscale_types::abi::AbiType {
                ::everscale_types::abi::AbiType::tuple(#abi_values_slice)
            }
        }
    };

    Ok(token_stream)
}

pub fn construct_with_abi_type(
    field_name: &syn::Ident,
    ty: &syn::Type,
    attrs: FieldAttributes,
) -> Result<proc_macro2::TokenStream, Error> {
    attrs.check()?;

    let to_change = match &attrs.custom_name {
        Some(custom) => custom.to_string(),
        None => field_name.to_string(),
    };
    let custom_name = to_change.to_string();

    for (ty, path) in &attrs.with_handlers {
        if !matches!(ty, HandlerType::AbiType) {
            continue;
        }

        return Ok(quote! {
            #path().named(#custom_name)
        });
    }

    //fallback to mod handler if present
    Ok(match &attrs.mod_handler {
        Some(handler) => quote!(#handler::abi_type().named(#custom_name)),
        None => quote!(<#ty>::abi_type().named(#custom_name)),
    })
}
