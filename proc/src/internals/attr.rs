use std::fmt::Formatter;

use proc_macro2::{Group, Span, TokenStream, TokenTree};
use quote::ToTokens;
use syn::Meta::{List, NameValue};
use syn::NestedMeta::{Lit, Meta};

use super::ctxt::*;
use super::symbol::*;

pub struct Container;

impl Container {
    pub fn from_ast(cx: &Ctxt, item: &syn::DeriveInput) -> Self {
        for meta_item in item
            .attrs
            .iter()
            .flat_map(|attr| get_meta_items(cx, attr))
            .flatten()
        {
            match &meta_item {
                (_, Meta(meta_item)) => {
                    let path = meta_item
                        .path()
                        .into_token_stream()
                        .to_string()
                        .replace(' ', "");
                    cx.error_spanned_by(
                        meta_item.path(),
                        format!("unknown container attribute `{path}`"),
                    );
                }
                (_, Lit(lit)) => {
                    cx.error_spanned_by(lit, "unexpected literal in container attribute");
                }
            }
        }

        Self
    }
}

pub struct Variant;

impl Variant {
    pub fn from_ast(cx: &Ctxt, item: &syn::Variant) -> Self {
        for meta_item in item
            .attrs
            .iter()
            .flat_map(|attr| get_meta_items(cx, attr))
            .flatten()
        {
            match &meta_item {
                (_, Meta(meta_item)) => {
                    let path = meta_item
                        .path()
                        .into_token_stream()
                        .to_string()
                        .replace(' ', "");
                    cx.error_spanned_by(
                        meta_item.path(),
                        format!("unknown variant attribute `{path}`"),
                    );
                }
                (_, Lit(lit)) => {
                    cx.error_spanned_by(lit, "unexpected literal in variant attribute");
                }
            }
        }

        Self
    }
}

pub struct Field {
    pub debug_with: Option<syn::Expr>,
}

impl Field {
    pub fn from_ast(cx: &Ctxt, field: &syn::Field) -> Self {
        let mut debug_with = Attr::none(cx, WITH);

        for meta_item in field
            .attrs
            .iter()
            .flat_map(|attr| get_meta_items(cx, attr))
            .flatten()
        {
            match &meta_item {
                // Parse `#[debug(with = "some_module"]`
                (MetaContext::Debug, Meta(NameValue(m))) if m.path == WITH => {
                    if let Ok(expr) = parse_lit_into_expr(cx, WITH, &m.lit) {
                        debug_with.set(&m.path, expr);
                    }
                }
                // Other
                (_, Meta(meta_item)) => {
                    let path = meta_item
                        .path()
                        .into_token_stream()
                        .to_string()
                        .replace(' ', "");
                    cx.error_spanned_by(
                        meta_item.path(),
                        format!("unknown field attribute `{path}`"),
                    );
                }
                (_, Lit(lit)) => {
                    cx.error_spanned_by(lit, "unexpected literal in field attribute");
                }
            }
        }

        let debug_with = debug_with.get();

        Self { debug_with }
    }
}

fn parse_lit_into_expr(cx: &Ctxt, attr_name: Symbol, lit: &syn::Lit) -> Result<syn::Expr, ()> {
    let string = get_lit_str(cx, attr_name, lit)?;

    parse_lit_str(string).map_err(|_| {
        cx.error_spanned_by(lit, format!("failed to parse expr: {:?}", string.value()))
    })
}

fn parse_lit_str<T>(s: &syn::LitStr) -> syn::parse::Result<T>
where
    T: syn::parse::Parse,
{
    let tokens = spanned_tokens(s)?;
    syn::parse2(tokens)
}

fn spanned_tokens(s: &syn::LitStr) -> syn::parse::Result<TokenStream> {
    let stream = syn::parse_str(&s.value())?;
    Ok(respan_token_stream(stream, s.span()))
}

fn respan_token_stream(stream: TokenStream, span: Span) -> TokenStream {
    stream
        .into_iter()
        .map(|token| respan_token_tree(token, span))
        .collect()
}

fn respan_token_tree(mut token: TokenTree, span: Span) -> TokenTree {
    if let TokenTree::Group(g) = &mut token {
        *g = Group::new(g.delimiter(), respan_token_stream(g.stream(), span));
    }
    token.set_span(span);
    token
}

fn get_lit_str<'a>(cx: &Ctxt, attr_name: Symbol, lit: &'a syn::Lit) -> Result<&'a syn::LitStr, ()> {
    if let syn::Lit::Str(lit) = lit {
        Ok(lit)
    } else {
        cx.error_spanned_by(
            lit,
            format!("expected {attr_name} attribute to be a string: `{attr_name} = \"...\"`",),
        );
        Err(())
    }
}

fn get_meta_items(
    cx: &Ctxt,
    attr: &syn::Attribute,
) -> Result<Vec<(MetaContext, syn::NestedMeta)>, ()> {
    let meta_context = if attr.path == DEBUG {
        MetaContext::Debug
    } else {
        return Ok(Vec::new());
    };

    match attr.parse_meta() {
        Ok(List(meta)) => Ok(meta
            .nested
            .into_iter()
            .map(|item| (meta_context, item))
            .collect()),
        Ok(other) => {
            cx.error_spanned_by(other, format!("expected #[{meta_context}(...)]"));
            Err(())
        }
        Err(err) => {
            cx.syn_error(err);
            Err(())
        }
    }
}

#[derive(Copy, Clone)]
enum MetaContext {
    Debug,
}

impl std::fmt::Display for MetaContext {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Debug => std::fmt::Display::fmt(&DEBUG, f),
        }
    }
}

#[allow(unused)]
struct BoolAttr<'c>(Attr<'c, ()>);

#[allow(unused)]
impl<'c> BoolAttr<'c> {
    fn none(cx: &'c Ctxt, name: Symbol) -> Self {
        BoolAttr(Attr::none(cx, name))
    }

    fn set_true<O>(&mut self, object: O)
    where
        O: ToTokens,
    {
        self.0.set(object, ());
    }

    fn get(&self) -> bool {
        self.0.value.is_some()
    }
}

struct Attr<'c, T> {
    cx: &'c Ctxt,
    name: Symbol,
    tokens: TokenStream,
    value: Option<T>,
}

impl<'c, T> Attr<'c, T> {
    fn none(cx: &'c Ctxt, name: Symbol) -> Self {
        Self {
            cx,
            name,
            tokens: TokenStream::new(),
            value: None,
        }
    }

    fn set<O>(&mut self, object: O, value: T)
    where
        O: ToTokens,
    {
        let tokens = object.into_token_stream();

        if self.value.is_some() {
            self.cx
                .error_spanned_by(tokens, format!("duplicated attribute `{}`", self.name));
        } else {
            self.tokens = tokens;
            self.value = Some(value);
        }
    }

    #[allow(unused)]
    fn set_opt<O>(&mut self, object: O, value: Option<T>)
    where
        O: ToTokens,
    {
        if let Some(value) = value {
            self.set(object, value);
        }
    }

    #[allow(unused)]
    fn set_if_none(&mut self, value: T) {
        if self.value.is_none() {
            self.value = Some(value);
        }
    }

    fn get(self) -> Option<T> {
        self.value
    }

    #[allow(unused)]
    fn get_with_tokens(self) -> Option<(TokenStream, T)> {
        match self.value {
            Some(value) => Some((self.tokens, value)),
            None => None,
        }
    }
}
