use proc_macro2::TokenStream;
use quote::quote;
use syn::Error;

use crate::internals::container::Container;
use crate::internals::context::Ctxt;
use crate::internals::field::{extract_field_attributes, FieldAttributes, StructField};

pub fn impl_derive(input: syn::DeriveInput) -> Result<TokenStream, Vec<Error>> {
    let ctx = Ctxt::new();
    let container_opt = Container::from_ast(&ctx, &input);

    let Some(container) = container_opt else {
        return Err(ctx.check().unwrap_err());
    };

    let Some(struct_fields) = construct_from_abi(&container.data.fields, &ctx) else {
        return Err(ctx.check().unwrap_err());
    };

    let ident = container.name_ident;
    let (impl_generics, ty_generics, where_clause) = container.generics.split_for_impl();

    let token_stream = quote! {
        impl #impl_generics ::everscale_types::abi::FromAbi for #ident #ty_generics #where_clause {
            fn from_abi(value: ::everscale_types::abi::AbiValue) -> everscale_types::abi::__export::anyhow::Result<Self> {
                let ::everscale_types::abi::AbiValue::Tuple(inner) = value else {
                     everscale_types::abi::__export::anyhow::bail!("AbiValue has incorrect type")
                };
                let mut iter = inner.iter();
                Ok(Self { #(#struct_fields),* })
            }
        }
    };

    Ok(token_stream)
}

pub fn construct_from_abi(fields: &syn::Fields, ctx: &Ctxt) -> Option<Vec<TokenStream>> {
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
    Some(struct_fields)
}

fn construct_from_abi_inner(
    struct_field: &StructField,
    attrs: &FieldAttributes,
    named: bool,
) -> TokenStream {
    let field_name = &struct_field.field_name;

    if let Some(path) = &attrs.with_handlers.from_abi_handler {
        let base = quote! {
             #path(
                iter.next()
                    .ok_or(everscale_types::abi::__export::anyhow::anyhow!("unable to get field from abi"))?.value.clone())?
        };

        return if named {
            quote! {
                 #field_name: #base
            }
        } else {
            base
        };
    }

    //fallback to mod handler if present
    match &attrs.mod_handler {
        Some(path) => {
            let base = quote!(#path::from_abi(
                    iter.next()
                    .ok_or(everscale_types::abi::__export::anyhow::anyhow!("unable to get field from abi"))?.value.clone())?);
            if named {
                quote!(#field_name: #base)
            } else {
                base
            }
        }
        None => {
            let base = quote!(<_>::from_abi(
                iter.next()
                    .ok_or(everscale_types::abi::__export::anyhow::anyhow!(
                        "unable to get field from abi"
                    ))?
                    .value
                    .clone()
            )?);
            if named {
                quote!(#field_name: #base)
            } else {
                base
            }
        }
    }
}
