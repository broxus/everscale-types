use crate::common;
use crate::common::FieldAttributes;
use quote::quote;

pub fn impl_derive(input: syn::DeriveInput) -> Result<proc_macro2::TokenStream, syn::Error> {
    let data = match input.data {
        syn::Data::Struct(data_struct) => data_struct,
        syn::Data::Enum(_) => {
            return Err(syn::Error::new_spanned(
                &input,
                "WithAbiType is not supported for enum",
            ))
        }
        syn::Data::Union(_) => {
            return Err(syn::Error::new_spanned(
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

        let attributes = common::extract_field_attributes(i.attrs.as_slice());
        let token = construct_with_abi_type(name, &i.ty, attributes);

        tuple.push(token);
    }

    let abi_values_slice = quote! {
        [ #(#tuple),* ]
    };

    let token_stream = quote! {
        impl WithAbiType for #ident {
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
) -> proc_macro2::TokenStream {
    let to_change = match &attrs.custom_name {
        Some(custom) => custom.to_string(),
        None => field_name.to_string(),
    };
    let custom_name = to_change.to_string();

    match &attrs.custom_handler {
        Some(handler) => quote!(#handler::abi_type(self.#field_name).named(#custom_name)),
        None => quote!(<#ty>::abi_type().named(#custom_name)),
    }
}
