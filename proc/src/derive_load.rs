use proc_macro2::TokenStream;
use quote::quote;

use crate::internals::{ast, attr, ctxt};
use crate::{bound, Derive};

pub fn impl_derive(input: syn::DeriveInput) -> Result<TokenStream, Vec<syn::Error>> {
    let cx = ctxt::Ctxt::new();
    let container = match ast::Container::from_ast(&cx, &input, Derive::Debug) {
        Some(container) => container,
        None => return Err(cx.check().unwrap_err()),
    };
    cx.check()?;

    let tlb_lifetime: syn::LifetimeDef = syn::parse_quote!('tlb);
    let cell_family: syn::Ident = quote::format_ident!("C");
    let cell_family_ty: syn::TypeParam =
        syn::parse_quote!(#cell_family: ::everscale_types::cell::CellFamily);

    let ident = &container.ident;
    let generics = bound::without_default(container.generics);
    let (_, ty_generics, where_clause) = generics.split_for_impl();

    let mut alt_generics = generics.clone();

    let mut has_tlb_lifetime = false;
    let mut has_cell_family = false;
    for param in alt_generics.params.iter() {
        match param {
            syn::GenericParam::Lifetime(def) => {
                has_tlb_lifetime |= def.lifetime == tlb_lifetime.lifetime;
            }
            syn::GenericParam::Type(ty) => {
                has_cell_family |= ty.ident == cell_family_ty.ident;
            }
            _ => {}
        }
    }

    if !has_tlb_lifetime {
        alt_generics
            .params
            .push(syn::GenericParam::Lifetime(tlb_lifetime.clone()));
    }
    if !has_cell_family {
        alt_generics
            .params
            .push(syn::GenericParam::Type(cell_family_ty));
    }
    let (impl_generics, _, _) = alt_generics.split_for_impl();

    let (inline, body) = match &container.data {
        ast::Data::Enum(variants) => (variants.len() < 2, build_enum(variants)),
        ast::Data::Struct(style, fields) => {
            let inline = fields.len() < 2;
            let body = build_struct(&container, &tlb_lifetime, &cell_family, *style, fields);
            (inline, body)
        }
    };

    let inline = if inline { quote!(#[inline]) } else { quote!() };

    let result = quote! {
        #[automatically_derived]
        impl #impl_generics ::everscale_types::cell::Load<#tlb_lifetime, #cell_family> for #ident #ty_generics #where_clause {
            #inline
            fn load_from(__slice: &mut ::everscale_types::cell::CellSlice<#tlb_lifetime, #cell_family>) -> Option<Self> {
                #body
            }
        }
    };

    Ok(result)
}

fn build_enum(_: &[ast::Variant<'_>]) -> TokenStream {
    panic!("Unsupported")
}

fn build_struct(
    container: &ast::Container<'_>,
    lifetime_def: &syn::LifetimeDef,
    cell_family: &syn::Ident,
    style: ast::Style,
    fields: &[ast::Field<'_>],
) -> TokenStream {
    let condition = container.attrs.tlb_tag.and_then(load_tag_op);

    let members = fields.iter().map(|field| {
        let ident = &field.member;
        let op = load_op(lifetime_def, cell_family, field.ty);
        quote! {
            #ident: #op
        }
    });

    let result = match style {
        ast::Style::Unit => quote!(Self),
        _ => quote! {
            Self {
                #(#members),*,
            }
        },
    };

    let result = match &container.attrs.tlb_validate_with {
        Some(expr) => quote! {
            let result = #result;
            if #expr(&result) {
                Some(result)
            } else {
                None
            }
        },
        None => quote!(Some(#result)),
    };

    quote! {
        #condition
        #result
    }
}

fn load_tag_op(tag: attr::TlbTag) -> Option<TokenStream> {
    let bits = tag.bits as u16;

    let neg_condition = match bits {
        0 => return None,
        1 if tag.value == 0 => quote!(__slice.load_bit()?),
        1 => quote!(!__slice.load_bit()?),
        2..=7 => {
            let value = tag.value as u8;
            quote!(__slice.load_small_uint(#bits)? != #value)
        }
        8 => {
            let value = tag.value as u8;
            quote!(__slice.load_u8()? != #value)
        }
        16 => {
            let value = tag.value as u16;
            quote!(__slice.load_u16()? != #value)
        }
        32 => {
            let value = tag.value;
            quote!(__slice.load_u32()? != #value)
        }
        _ => {
            let value = tag.value as u64;
            quote!(__slice.load_uint(#bits) != #value)
        }
    };

    Some(quote!(
        if #neg_condition {
            return None;
        }
    ))
}

fn load_op(
    lifetime_def: &syn::LifetimeDef,
    cell_family: &syn::Ident,
    ty: &syn::Type,
) -> TokenStream {
    #[allow(clippy::unnecessary_operation)]
    'fallback: {
        match ty {
            syn::Type::Path(syn::TypePath { path, .. }) => {
                if let Some(syn::PathSegment { ident, .. }) = path.segments.last() {
                    let op = match ident.to_string().as_str() {
                        "bool" => quote!(load_bit()?),
                        "i8" => quote!(load_u8()? as i8),
                        "u8" => quote!(load_u8()?),
                        "i16" => quote!(load_u16()? as i16),
                        "u16" => quote!(load_u16()?),
                        "i32" => quote!(load_u32()? as i32),
                        "u32" => quote!(load_u32()?),
                        "i64" => quote!(load_u64()? as i64),
                        "u64" => quote!(load_u64()?),
                        "CellHash" => quote!(load_u256()?),
                        "Cell" => quote!(load_reference()?),
                        "CellContainer" => quote!(load_reference_cloned()?),
                        _ => break 'fallback,
                    };

                    return quote!(__slice.#op);
                }
            }
            syn::Type::Reference(syn::TypeReference { elem, .. }) => {
                return load_op(lifetime_def, cell_family, elem);
            }
            _ => break 'fallback,
        }
    };

    quote! { <#ty as ::everscale_types::cell::Load<#lifetime_def, #cell_family>>::load_from(__slice)? }
}
