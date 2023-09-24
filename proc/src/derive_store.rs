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

    let ident = &container.ident;
    let generics = bound::without_default(container.generics);
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    let (inline, body) = match &container.data {
        ast::Data::Enum(variants) => (variants.len() < 2, build_enum(variants)),
        ast::Data::Struct(style, fields) => {
            (fields.len() < 2, build_struct(&container, *style, fields))
        }
    };

    let inline = if inline { quote!(#[inline]) } else { quote!() };

    let result = quote! {
        #[automatically_derived]
        impl #impl_generics ::everscale_types::cell::Store for #ident #ty_generics #where_clause {
            #inline
            fn store_into(
                &self,
                __builder: &mut ::everscale_types::cell::CellBuilder,
                __context: &mut dyn ::everscale_types::cell::CellContext,
            ) -> ::core::result::Result<(), ::everscale_types::error::Error> {
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
    style: ast::Style,
    fields: &[ast::Field<'_>],
) -> TokenStream {
    let store_tag = container.attrs.tlb_tag.and_then(store_tag_op);

    let fields_len = fields.len();
    let members = fields.iter().enumerate().map(|(i, field)| {
        let ident = &field.member;
        let field_ident = quote!(self.#ident);
        let op = store_op(&field_ident, field.ty);
        if i + 1 == fields_len {
            op
        } else {
            into_ok(op)
        }
    });

    match style {
        ast::Style::Unit => match store_tag {
            Some(store_tag) => store_tag,
            None => quote!(::core::result::Result::Ok(())),
        },
        _ => {
            let validate_with = container.attrs.tlb_validate_with.as_ref().map(|expr| {
                quote!(if !#expr(self) {
                    return ::core::result::Result::Err(::everscale_types::error::Error::InvalidData);
                })
            });
            let store_tag = store_tag.map(into_ok);
            quote! {
                #validate_with
                #store_tag
                #(#members)*
            }
        }
    }
}

fn store_tag_op(tag: attr::TlbTag) -> Option<TokenStream> {
    let bits = tag.bits as u16;

    let op = match bits {
        0 => return None,
        1 if tag.value == 0 => quote!(store_bit_zero()),
        1 => quote!(store_bit_one()),
        2..=7 => {
            let value = tag.value as u8;
            quote!(store_small_uint(#value, #bits))
        }
        8 => {
            let value = tag.value as u8;
            quote!(store_u8(#value))
        }
        16 => {
            let value = tag.value as u16;
            quote!(store_u16(#value))
        }
        32 => {
            let value = tag.value;
            quote!(store_u32(#value))
        }
        _ => {
            let value = tag.value as u64;
            quote!(store_uint(#value, #bits))
        }
    };
    Some(quote!(__builder.#op))
}

fn store_op(field_ident: &TokenStream, ty: &syn::Type) -> TokenStream {
    #[allow(clippy::unnecessary_operation)]
    'fallback: {
        match ty {
            syn::Type::Path(syn::TypePath { path, .. }) => {
                if let Some(syn::PathSegment { ident, .. }) = path.segments.last() {
                    let op = match ident.to_string().as_str() {
                        "bool" => quote!(store_bit(#field_ident)),
                        "i8" => quote!(store_u8(#field_ident as u8)),
                        "u8" => quote!(store_u8(#field_ident)),
                        "i16" => quote!(store_u16(#field_ident as u16)),
                        "u16" => quote!(store_u16(#field_ident)),
                        "i32" => quote!(store_u32(#field_ident as u32)),
                        "u32" => quote!(store_u32(#field_ident)),
                        "i64" => quote!(store_u64(#field_ident as u64)),
                        "u64" => quote!(store_u64(#field_ident)),
                        "NonZeroU8" => quote!(store_u8(#field_ident.get())),
                        "NonZeroU16" => quote!(store_u16(#field_ident.get())),
                        "NonZeroU32" => quote!(store_u32(#field_ident.get())),
                        "HashBytes" => quote!(store_u256(&#field_ident)),
                        "CellContainer" => quote!(store_reference(#field_ident.clone())),
                        _ => break 'fallback,
                    };

                    return quote!(__builder.#op);
                }
            }
            syn::Type::Reference(syn::TypeReference { elem, .. }) => {
                return store_op(field_ident, elem);
            }
            _ => break 'fallback,
        }
    };

    quote! { <#ty as ::everscale_types::cell::Store>::store_into(&#field_ident, __builder, __context) }
}

fn into_ok(tokens: TokenStream) -> TokenStream {
    quote!(match #tokens {
        ::core::result::Result::Ok(_) => {},
        ::core::result::Result::Err(err) => return ::core::result::Result::Err(err),
    })
}
