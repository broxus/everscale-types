use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

use crate::internals::{ast, ctxt};
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

    let body = match &container.data {
        ast::Data::Enum(variants) => build_enum(variants),
        ast::Data::Struct(style, fields) => build_struct(*style, fields),
    };

    let result = quote! {
        #[automatically_derived]
        impl #impl_generics ::core::cmp::Eq for #ident #ty_generics #where_clause {}

        #[automatically_derived]
        impl #impl_generics ::core::cmp::PartialEq for #ident #ty_generics #where_clause {
            #[inline]
            fn eq(&self, __other: &Self) -> bool {
                #body
            }
        }
    };

    Ok(result)
}

fn build_enum(variants: &[ast::Variant<'_>]) -> TokenStream {
    let variants = variants.iter().map(|variant| {
        let variant_name = &variant.ident;

        match &variant.style {
            ast::Style::Struct => {
                let destructed = variant
                    .fields
                    .iter()
                    .map(|field| {
                        let ident = &field.member;
                        let ident_str = field.member_name();
                        let self_ident = quote::format_ident!("__self_{ident_str}");
                        let other_ident = quote::format_ident!("__other_{ident_str}");
                        (
                            quote! { #ident: #self_ident },
                            quote! { #ident: #other_ident },
                        )
                    })
                    .collect::<Vec<_>>();

                let operations = destructed.iter().map(|(member_self, member_other)| {
                    quote! { *#member_self == *#member_other }
                });

                if variant.fields.is_empty() {
                    quote! { (Self::#variant_name, Self::#variant_name) => true }
                } else {
                    let destructed_self = destructed.iter().map(|(x, _)| x);
                    let destructed_other = destructed.iter().map(|(_, x)| x);
                    quote! {
                        (
                            Self::#variant_name { #(#destructed_self),*, },
                            Self::#variant_name { #(#destructed_other),*, }
                        ) => #(#operations)&&*
                    }
                }
            }
            ast::Style::Tuple => {
                let destructed = (0..variant.fields.len())
                    .map(|i| {
                        let self_ident = quote::format_ident!("__self_{i}").to_token_stream();
                        let other_ident = quote::format_ident!("__other_{i}").to_token_stream();
                        (self_ident, other_ident)
                    })
                    .collect::<Vec<_>>();

                let operations = destructed.iter().map(|(member_self, member_other)| {
                    quote! { *#member_self == *#member_other }
                });

                let destructed_self = destructed.iter().map(|(x, _)| x);
                let destructed_other = destructed.iter().map(|(_, x)| x);

                quote! {
                    (
                        Self::#variant_name(#(#destructed_self),*),
                        Self::#variant_name(#(#destructed_other),*)
                    ) => #(#operations)&&*
                }
            }
            ast::Style::Unit => quote! { (Self::#variant_name, Self::#variant_name) => true },
        }
    });

    quote! {
        let __self_tag = ::core::mem::discriminant(self);
        let __other_tag = ::core::mem::discriminant(__other);
        __self_tag == __other_tag
            && match (self, __other) {
                #(#variants),*,
                // SAFETY: discriminants are equal
                _ => unsafe{ ::core::hint::unreachable_unchecked() }
            }
    }
}

fn build_struct(style: ast::Style, fields: &[ast::Field<'_>]) -> TokenStream {
    let members = fields.iter().map(|field| {
        let field = &field.member;
        quote! { self.#field == __other.#field }
    });

    match style {
        ast::Style::Unit => quote!(true),
        _ => quote! {
            #(#members)&&*
        },
    }
}
