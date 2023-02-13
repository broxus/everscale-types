use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

use crate::internals::{ast, ctxt};
use crate::{bound, Derive};

pub fn impl_derive_debug(input: syn::DeriveInput) -> Result<TokenStream, Vec<syn::Error>> {
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
        ast::Data::Struct(style, fields) => build_struct(&container, *style, fields),
    };

    let result = quote! {
        #[automatically_derived]
        impl #impl_generics ::core::fmt::Debug for #ident #ty_generics #where_clause {
            #body
        }
    };

    Ok(result)
}

fn build_enum(variants: &[ast::Variant<'_>]) -> TokenStream {
    let variants = variants.iter().map(|variant| {
        let variant_name = &variant.ident;

        let destructed = match &variant.style {
            ast::Style::Struct => {
                let fields = variant
                    .fields
                    .iter()
                    .map(|field| {
                        let ident = &field.member;
                        quote! { #ident }
                    })
                    .collect::<Vec<_>>();

                if fields.is_empty() {
                    quote! { #variant_name }
                } else {
                    quote! { #variant_name { #(#fields),*, } }
                }
            }
            ast::Style::Tuple => {
                let fields = variant
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(i, _)| quote::format_ident!("field_{}", i).to_token_stream());

                quote! { #variant_name(#(#fields),*) }
            }
            ast::Style::Unit => quote! { #variant_name },
        };

        let body = build_fmt(
            &variant.ident,
            variant.style,
            &variant.fields,
            |field| match &field.member {
                syn::Member::Named(ident) => ident.to_token_stream(),
                syn::Member::Unnamed(i) => quote::format_ident!("field_{}", i).to_token_stream(),
            },
        );
        quote! { Self::#destructed => #body, }
    });

    quote! {
        fn fmt(&self, __f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
            match self {
                #(#variants)*
            }
        }
    }
}

fn build_struct(
    container: &ast::Container<'_>,
    style: ast::Style,
    fields: &[ast::Field<'_>],
) -> TokenStream {
    let body = build_fmt(&container.ident, style, fields, |field| {
        let field = &field.member;
        quote! { self.#field }
    });

    quote! {
        fn fmt(&self, __f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
            #body
        }
    }
}

fn build_fmt<F>(
    ident: &syn::Ident,
    style: ast::Style,
    fields: &[ast::Field<'_>],
    mut f: F,
) -> TokenStream
where
    F: FnMut(&ast::Field) -> TokenStream,
{
    fn build_field_ref<F>(field: &ast::Field<'_>, f: &mut F) -> TokenStream
    where
        F: FnMut(&ast::Field) -> TokenStream,
    {
        let ident = f(field);
        if let Some(with) = &field.attrs.debug_with {
            quote! { &#with(&#ident) }
        } else {
            quote! { &#ident }
        }
    }

    let ident_str = ident.to_string();

    let mut make_args = || match style {
        ast::Style::Unit => Vec::new(),
        ast::Style::Tuple => fields
            .iter()
            .map(|field| build_field_ref(field, &mut f))
            .collect(),
        ast::Style::Struct => fields
            .iter()
            .map(|field| {
                let field_str = field.member_name();
                let field = build_field_ref(field, &mut f);
                quote! { #field_str, #field }
            })
            .collect(),
    };

    match (style, fields.len()) {
        (ast::Style::Unit, _) | (_, 0) => {
            quote! { ::core::fmt::Formatter::write_str(__f, #ident_str) }
        }
        (ast::Style::Tuple, 1) => {
            let args = make_args();
            quote! { crate::util::debug_tuple_field1_finish(__f, #ident_str, #(#args),*) }
        }
        (ast::Style::Tuple, 2) => {
            let args = make_args();
            quote! { crate::util::debug_tuple_field2_finish(__f, #ident_str, #(#args),*) }
        }
        (ast::Style::Tuple, _) => {
            let values = fields.iter().map(|field| build_field_ref(field, &mut f));
            quote! {
                {
                    let values: &[&dyn ::core::fmt::Debug] = &[#(#values),*];
                    crate::util::debug_tuple_fields_finish(__f, #ident_str, values)
                }
            }
        }
        (ast::Style::Struct, 1) => {
            let args = make_args();
            quote! { crate::util::debug_struct_field1_finish(__f, #ident_str, #(#args),*) }
        }
        (ast::Style::Struct, 2) => {
            let args = make_args();
            quote! { crate::util::debug_struct_field2_finish(__f, #ident_str, #(#args),*) }
        }
        (ast::Style::Struct, 3) => {
            let args = make_args();
            quote! { crate::util::debug_struct_field3_finish(__f, #ident_str, #(#args),*) }
        }
        (ast::Style::Struct, 4) => {
            let args = make_args();
            quote! { crate::util::debug_struct_field4_finish(__f, #ident_str, #(#args),*) }
        }
        (ast::Style::Struct, 5) => {
            let args = make_args();
            quote! { crate::util::debug_struct_field5_finish(__f, #ident_str, #(#args),*) }
        }
        (ast::Style::Struct, _) => {
            let names = fields.iter().map(ast::Field::member_name);
            let values = fields.iter().map(|field| build_field_ref(field, &mut f));

            quote! {
                {
                    let names: &[&'static _] = &[#(#names),*];
                    let values: &[&dyn ::core::fmt::Debug] = &[#(#values),*];
                    crate::util::debug_struct_fields_finish(__f, #ident_str, names, values)
                }
            }
        }
    }
}
