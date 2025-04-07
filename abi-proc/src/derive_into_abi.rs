use proc_macro2::TokenStream;
use quote::quote;
use syn::{Error, Fields};

use crate::internals::container::Container;
use crate::internals::context::Ctxt;
use crate::internals::field::{extract_field_attributes, FieldAttributes, StructField};

pub fn impl_derive(input: syn::DeriveInput) -> Result<TokenStream, Vec<Error>> {
    let ctx = Ctxt::new();
    let container_opt = Container::from_ast(&ctx, &input);
    let Some(container) = container_opt else {
        return Err(ctx.check().unwrap_err());
    };
    let Some(tuple) = construct_into_abi(&container.data.fields, &ctx) else {
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

fn construct_into_abi(fields: &Fields, ctx: &Ctxt) -> Option<Vec<TokenStream>> {
    let mut struct_fields = Vec::new();

    for (index, field) in fields.iter().enumerate() {
        let struct_field = match &field.ident {
            Some(named) => StructField::named(named),
            None => StructField::unnamed(index),
        };

        let attributes = extract_field_attributes(ctx, field.attrs.as_slice());

        if !attributes.extracted {
            return None;
        }

        let token = construct_named_abi_value_inner(&struct_field, &attributes);

        struct_fields.push(token);
    }
    Some(struct_fields)
}

fn construct_named_abi_value_inner(
    struct_field: &StructField,
    custom_attributes: &FieldAttributes,
) -> TokenStream {
    let to_change = match &custom_attributes.custom_name {
        Some(custom) => custom,
        None => &struct_field.name_ident,
    };

    let custom_name = to_change.to_string();

    let field_name = &struct_field.field_name;
    if let Some(path) = &custom_attributes.with_handlers.into_abi_handler {
        return quote! {
            quote!(#path(&self.#field_name).named(#custom_name))
        };
    }

    //fallback to mod handler if present
    match &custom_attributes.mod_handler {
        Some(handler) => {
            quote!(#handler::as_abi(&self.#field_name).named(#custom_name))
        }
        None => {
            quote!(self.#field_name.as_abi().named(#custom_name))
        }
    }
}
