use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

use crate::internals::{ast, ctxt};
use crate::{bound, Derive};

pub fn impl_derive_clone(input: syn::DeriveInput) -> Result<TokenStream, Vec<syn::Error>> {
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
        impl #impl_generics ::core::clone::Clone for #ident #ty_generics #where_clause {
            #[inline]
            fn clone(&self) -> Self {
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
                let destructed = variant.fields.iter().map(|field| {
                    let ident = &field.member;
                    quote! { #ident }
                });

                let members = variant.fields.iter().map(|field| {
                    let field = &field.member;
                    quote! { #field: ::core::clone::Clone::clone(#field) }
                });

                if variant.fields.is_empty() {
                    quote! { Self::#variant_name => Self::#variant_name }
                } else {
                    quote! {
                        Self::#variant_name { #(#destructed),*, } => Self::#variant_name {
                            #(#members),*
                        }
                    }
                }
            }
            ast::Style::Tuple => {
                let fields = variant
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, _)| quote::format_ident!("field_{}", i).to_token_stream());

                let members = fields.clone().map(|field| {
                    quote! { ::core::clone::Clone::clone(#field) }
                });

                quote! { Self::#variant_name(#(#fields),*) => Self::#variant_name(#(#members),*) }
            }
            ast::Style::Unit => quote! { Self::#variant_name => Self::#variant_name },
        }
    });

    quote! {
        match self {
            #(#variants),*,
        }
    }
}

fn build_struct(style: ast::Style, fields: &[ast::Field<'_>]) -> TokenStream {
    let members = fields.iter().map(|field| {
        let field = &field.member;
        quote! { #field: ::core::clone::Clone::clone(&self.#field) }
    });

    match style {
        ast::Style::Unit => quote!(Self),
        _ => quote! {
            Self {
                #(#members),*,
            }
        },
    }
}
