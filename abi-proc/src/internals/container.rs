use proc_macro2::TokenStream;
use quote::quote;
use syn::DataStruct;

use crate::internals::common;
use crate::internals::common::FieldAttributes;
use crate::internals::context::Ctxt;
use crate::internals::field::StructField;

pub struct Container<'a> {
    pub name_ident: &'a syn::Ident,
    pub generics: syn::Generics,
    pub data: DataStruct,
}

impl<'a> Container<'a> {
    pub fn from_ast(ctx: &'a Ctxt, input: &'a syn::DeriveInput) -> Option<Self> {
        let data = match &input.data {
            syn::Data::Struct(data_struct) => data_struct,
            syn::Data::Enum(_) => {
                ctx.error_spanned_by(input, "FromAbi is not supported for enum");
                return None;
            }
            syn::Data::Union(_) => {
                ctx.error_spanned_by(input, "FromAbi is not supported for unions");
                return None;
            }
        };

        let generics = without_default_generic(&input.generics);
        let name_ident = &input.ident;

        Some(Self {
            name_ident,
            generics,
            data: data.clone(),
        })
    }

    pub fn construct_from_abi(&self, ctx: &Ctxt) -> Option<Vec<TokenStream>> {
        let mut struct_fields = Vec::new();

        let mut named = true;
        for (index, field) in self.data.fields.iter().enumerate() {
            let struct_field = match &field.ident {
                Some(named) => StructField::named(named),
                None => {
                    named = false;
                    StructField::unnamed(index)
                }
            };

            let attributes = common::extract_field_attributes(ctx, field.attrs.as_slice());

            if !attributes.extracted {
                return None;
            }

            let token = construct_from_abi_inner(&struct_field, &attributes, named);

            struct_fields.push(token);
        }
        Some(struct_fields)
    }

    pub fn construct_into_abi(&self, ctx: &Ctxt) -> Option<Vec<TokenStream>> {
        let mut struct_fields = Vec::new();

        for (index, field) in self.data.fields.iter().enumerate() {
            let struct_field = match &field.ident {
                Some(named) => StructField::named(named),
                None => StructField::unnamed(index),
            };

            let attributes = common::extract_field_attributes(ctx, field.attrs.as_slice());

            if !attributes.extracted {
                return None;
            }

            let token = construct_named_abi_value_inner(&struct_field, &attributes);

            struct_fields.push(token);
        }
        Some(struct_fields)
    }

    pub fn construct_with_abi_type(&self, ctx: &Ctxt) -> Option<Vec<TokenStream>> {
        let mut tuple = Vec::new();

        for (index, field) in self.data.fields.iter().enumerate() {
            let struct_field = match &field.ident {
                Some(named) => StructField::named(named),
                None => StructField::unnamed(index),
            };

            let attributes = common::extract_field_attributes(ctx, field.attrs.as_slice());

            if !attributes.extracted {
                return None;
            }
            let token = construct_with_abi_type_inner(&struct_field, &field.ty, attributes);

            tuple.push(token);
        }

        Some(tuple)
    }
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
                    .ok_or(anyhow::anyhow!("unable to get field from abi"))?.value.clone())?
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
                    .ok_or(anyhow::anyhow!("unable to get field from abi"))?.value.clone())?);
            if named {
                quote!(#field_name: #base)
            } else {
                base
            }
        }
        None => {
            let base = quote!(<_>::from_abi(
                iter.next()
                    .ok_or(anyhow::anyhow!("unable to get field from abi"))?
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

fn construct_with_abi_type_inner(
    struct_field: &StructField,
    ty: &syn::Type,
    attrs: FieldAttributes,
) -> TokenStream {
    let to_change = match &attrs.custom_name {
        Some(custom) => custom,
        None => &struct_field.name_ident,
    };
    let custom_name = to_change.to_string();

    if let Some(path) = &attrs.with_handlers.abi_type_handler {
        return quote! {
            #path().named(#custom_name)
        };
    }

    //fallback to mod handler if present
    match &attrs.mod_handler {
        Some(handler) => quote!(#handler::abi_type().named(#custom_name)),
        None => quote!(<#ty>::abi_type().named(#custom_name)),
    }
}

fn without_default_generic(generics: &syn::Generics) -> syn::Generics {
    syn::Generics {
        params: generics
            .params
            .iter()
            .map(|param| match param {
                syn::GenericParam::Type(param) => syn::GenericParam::Type(syn::TypeParam {
                    eq_token: None,
                    default: None,
                    ..param.clone()
                }),
                _ => param.clone(),
            })
            .collect(),
        ..generics.clone()
    }
}
