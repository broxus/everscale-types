use proc_macro2::TokenStream;
use quote::quote;
use syn::Fields;

use crate::internals::container;
use crate::internals::container::Container;
use crate::internals::context::Ctxt;
use crate::internals::field::{extract_field_attributes, FieldAttributes, StructField};

pub fn impl_derive(input: syn::DeriveInput) -> Result<TokenStream, Vec<syn::Error>> {
    let ctx = Ctxt::new();
    let Some(container) = Container::from_ast(&ctx, &input) else {
        return Err(ctx.check().unwrap_err());
    };

    let Some(tuple) = construct_with_abi_type(&container.data.fields, &ctx) else {
        return Err(ctx.check().unwrap_err());
    };

    let generics = container::with_bound(
        &container.data.fields,
        &container.generics,
        &syn::parse_quote!(::everscale_types::abi::WithAbiType),
    );

    let ident = &input.ident;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let abi_values = quote! {
        vec![#(#tuple),*]
    };

    let token_stream = quote! {
        impl #impl_generics ::everscale_types::abi::WithAbiType for #ident #ty_generics #where_clause {
            fn abi_type() -> ::everscale_types::abi::AbiType {
                ::everscale_types::abi::AbiType::Tuple(::std::sync::Arc::from(#abi_values))
            }
        }
    };

    Ok(token_stream)
}

fn construct_with_abi_type(fields: &Fields, ctx: &Ctxt) -> Option<Vec<TokenStream>> {
    let mut tuple = Vec::new();

    for (index, field) in fields.iter().enumerate() {
        let struct_field = match &field.ident {
            Some(named) => StructField::named(named),
            None => StructField::unnamed(index),
        };

        let attributes = extract_field_attributes(ctx, field.attrs.as_slice());
        if !attributes.extracted {
            return None;
        }

        let token = construct_with_abi_type_inner(&struct_field, &field.ty, attributes);
        tuple.push(token);
    }

    Some(tuple)
}

fn construct_with_abi_type_inner(
    struct_field: &StructField,
    ty: &syn::Type,
    attrs: FieldAttributes,
) -> TokenStream {
    let name = match &attrs.custom_name {
        Some(custom) => custom,
        None => &struct_field.name_ident,
    }
    .to_string();

    let extractor = if let Some(path) = &attrs.with_handlers.abi_type_handler {
        quote! { #path }
    } else if let Some(path) = &attrs.mod_handler {
        quote! { #path::abi_type }
    } else {
        quote! { <#ty as ::everscale_types::abi::WithAbiType>::abi_type }
    };

    quote! { #extractor().named(#name) }
}
