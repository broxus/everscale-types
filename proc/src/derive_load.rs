use proc_macro2::TokenStream;
use quote::quote;

use crate::internals::{ast, ctxt};
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
    let cell_family_ty: syn::TypeParam = syn::parse_quote!(#cell_family: crate::cell::CellFamily);

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
            let body = build_struct(&tlb_lifetime, &cell_family, *style, fields);
            (inline, body)
        }
    };

    let inline = if inline { quote!(#[inline]) } else { quote!() };

    let result = quote! {
        #[automatically_derived]
        impl #impl_generics crate::cell::Load<#tlb_lifetime, #cell_family> for #ident #ty_generics #where_clause {
            #inline
            fn load_from(__slice: &mut crate::cell::CellSlice<#tlb_lifetime, #cell_family>) -> Option<Self> {
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
    lifetime_def: &syn::LifetimeDef,
    cell_family: &syn::Ident,
    style: ast::Style,
    fields: &[ast::Field<'_>],
) -> TokenStream {
    let members = fields.iter().map(|field| {
        let ident = &field.member;
        let op = load_op(lifetime_def, cell_family, field.ty);
        quote! {
            #ident: #op
        }
    });

    match style {
        ast::Style::Unit => quote!(Some(Self)),
        _ => quote! {
            Some(Self {
                #(#members),*,
            })
        },
    }
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
                return load_op(lifetime_def, cell_family, elem)
            }
            _ => break 'fallback,
        }
    };

    quote! { <#ty as crate::cell::Load<#lifetime_def, #cell_family>>::load_from(__slice)? }
}
