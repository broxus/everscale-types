use proc_macro2::TokenStream;
use quote::quote;
use syn::{Error, Fields};

use crate::internals::container;
use crate::internals::container::Container;
use crate::internals::context::Ctxt;
use crate::internals::field::{extract_field_attributes, FieldAttributes, StructField};

pub fn impl_derive(input: syn::DeriveInput) -> Result<TokenStream, Vec<Error>> {
    let ctx = Ctxt::new();
    let container_opt = Container::from_ast(&ctx, &input);
    let Some(container) = container_opt else {
        return Err(ctx.check().unwrap_err());
    };
    let Some((into_fields, as_fields)) = construct_into_abi(&container.data.fields, &ctx) else {
        return Err(ctx.check().unwrap_err());
    };

    let into_abi_items = quote! {
        vec![#(#into_fields),*]
    };
    let as_abi_items = quote! {
        vec![#(#as_fields),*]
    };

    let generics = container::with_bound(
        &container.data.fields,
        &container.generics,
        &syn::parse_quote!(::tycho_types::abi::IntoAbi),
    );

    let ident = container.name_ident;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let token_stream = quote! {
        impl #impl_generics ::tycho_types::abi::IntoAbi for #ident #ty_generics #where_clause {
            fn into_abi(self) -> ::tycho_types::abi::AbiValue
            where
                Self: Sized,
            {
                ::tycho_types::abi::AbiValue::Tuple(#into_abi_items)
            }

            fn as_abi(&self) -> ::tycho_types::abi::AbiValue {
                ::tycho_types::abi::AbiValue::Tuple(#as_abi_items)
            }
        }
    };

    Ok(token_stream)
}

fn construct_into_abi(fields: &Fields, ctx: &Ctxt) -> Option<(Vec<TokenStream>, Vec<TokenStream>)> {
    let mut into_fields = Vec::new();
    let mut as_fields = Vec::new();

    for (index, field) in fields.iter().enumerate() {
        let struct_field = match &field.ident {
            Some(named) => StructField::named(named),
            None => StructField::unnamed(index),
        };

        let attributes = extract_field_attributes(ctx, field.attrs.as_slice());
        if !attributes.extracted {
            return None;
        }

        let (into_abi, as_abi) = construct_named_abi_value_inner(&struct_field, &attributes);
        into_fields.push(into_abi);
        as_fields.push(as_abi);
    }

    Some((into_fields, as_fields))
}

// Returns `into_abi` and `as_abi` items.
fn construct_named_abi_value_inner(
    struct_field: &StructField,
    custom_attributes: &FieldAttributes,
) -> (TokenStream, TokenStream) {
    let name = match &custom_attributes.custom_name {
        Some(custom) => custom,
        None => &struct_field.name_ident,
    }
    .to_string();

    let field_name = &struct_field.field_name;

    let (into_abi, as_abi) = if let Some(path) = &custom_attributes.with_handlers.into_abi_handler {
        let path_as_abi = custom_attributes
            .with_handlers
            .as_abi_handler
            .as_ref()
            .expect("must be checked");

        (
            quote! { #path(self.#field_name) },
            quote! { #path_as_abi(&self.#field_name) },
        )
    } else if let Some(path) = &custom_attributes.with_handlers.as_abi_handler {
        (
            quote! { #path(&self.#field_name) },
            quote! { #path(&self.#field_name) },
        )
    } else if let Some(path) = &custom_attributes.mod_handler {
        (
            quote! { #path::into_abi(self.#field_name) },
            quote! { #path::as_abi(&self.#field_name) },
        )
    } else {
        let path = quote! { ::tycho_types::abi::IntoAbi };
        (
            quote! { #path::into_abi(self.#field_name) },
            quote! { #path::as_abi(&self.#field_name) },
        )
    };

    (
        quote! { #into_abi.named(#name) },
        quote! { #as_abi.named(#name) },
    )
}
