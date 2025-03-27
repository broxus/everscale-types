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
        let Some(name) = i.ident else {
            continue;
        };
        let token = construct_with_abi_type_named(&name, &i.ty);
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

pub fn construct_with_abi_type_named(
    name_ident: &syn::Ident,
    ty: &syn::Type,
) -> proc_macro2::TokenStream {
    let str_name = name_ident.to_string();
    quote!(<#ty>::abi_type().named(#str_name))
}
