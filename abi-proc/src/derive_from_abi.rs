use proc_macro2::TokenStream;
use quote::quote;
use syn::Error;

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

    let Some((named, struct_fields)) = construct_from_abi(&container.data.fields, &ctx) else {
        return Err(ctx.check().unwrap_err());
    };

    let generics = container::with_bound(
        &container.data.fields,
        &container.generics,
        &syn::parse_quote!(::everscale_types::abi::FromAbi),
    );

    let ident = container.name_ident;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let slf = if named {
        quote!(Ok(Self { #(#struct_fields),* }))
    } else {
        quote!(Ok(Self ( #(#struct_fields),* )))
    };

    let token_stream = quote! {
        impl #impl_generics ::everscale_types::abi::FromAbi for #ident #ty_generics #where_clause {
            fn from_abi(value: ::everscale_types::abi::AbiValue) -> everscale_types::abi::__export::anyhow::Result<Self> {
                let ::everscale_types::abi::AbiValue::Tuple(inner) = value else {
                    return Err(everscale_types::abi::__export::anyhow::anyhow!(
                        "expected tuple while parsing AbiValue"
                    ));
                };
                let mut __iter = inner.into_iter();
                #slf
            }
        }
    };

    Ok(token_stream)
}

pub fn construct_from_abi(fields: &syn::Fields, ctx: &Ctxt) -> Option<(bool, Vec<TokenStream>)> {
    let mut struct_fields = Vec::new();

    let mut named = true;
    for (index, field) in fields.iter().enumerate() {
        let struct_field = match &field.ident {
            Some(named) => StructField::named(named),
            None => {
                named = false;
                StructField::unnamed(index)
            }
        };

        let attributes = extract_field_attributes(ctx, field.attrs.as_slice());
        if !attributes.extracted {
            return None;
        }

        let token = construct_from_abi_inner(&struct_field, &attributes, named);
        struct_fields.push(token);
    }

    Some((named, struct_fields))
}

fn construct_from_abi_inner(
    struct_field: &StructField,
    attrs: &FieldAttributes,
    named: bool,
) -> TokenStream {
    let field_name = &struct_field.field_name;

    let extractor = if let Some(path) = &attrs.with_handlers.from_abi_handler {
        quote! { #path }
    } else if let Some(path) = &attrs.mod_handler {
        quote! { #path::from_abi }
    } else {
        quote! { <_ as ::everscale_types::abi::FromAbi>::from_abi }
    };

    let base = quote! {
        match __iter.next() {
            Some(__item) => #extractor(__item.value)?,
            None => return Err(everscale_types::abi::__export::anyhow::anyhow!(
                "not enough tuple items while parsing AbiValue",
            )),
        }
    };

    if named {
        quote! {
            #field_name: #base
        }
    } else {
        base
    }
}
