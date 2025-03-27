use quote::quote;
use syn::{Fields, FieldsNamed};

pub fn impl_derive(input: syn::DeriveInput) -> Result<proc_macro2::TokenStream, syn::Error> {
    let data = match &input.data {
        syn::Data::Struct(data_struct) => data_struct,
        syn::Data::Enum(_) => {
            return Err(syn::Error::new_spanned(
                &input,
                "FromAbi is not supported for enum",
            ))
        }
        syn::Data::Union(_) => {
            return Err(syn::Error::new_spanned(
                &input,
                "FromAbi is not supported for unions",
            ))
        }
    };

    let ident = &input.ident;

    let fields = match &data.fields {
        Fields::Named(FieldsNamed { named, .. }) => {
            let mut fields = Vec::new();
            for i in named {
                let Some(name) = &i.ident else {
                    return Err(syn::Error::new_spanned(
                        &input,
                        "FromAbi does not support unnamed fields ",
                    ));
                };
                fields.push(quote!(#name));
            }
            fields
        }
        _ => {
            return Err(syn::Error::new_spanned(
                &input,
                "FromAbi does not support unnamed fields ",
            ))
        }
    };

    let token_stream = quote! {
        impl ::everscale_types::abi::FromAbi for #ident {
            fn from_abi(value: ::everscale_types::abi::AbiValue) -> anyhow::Result<Self> {
                let (#(#fields),*) = <_>::from_abi(value)?;
                Ok(Self { #(#fields),* })
            }
        }
    };

    Ok(token_stream)
}
