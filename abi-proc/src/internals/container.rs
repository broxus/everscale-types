use syn::DataStruct;

use crate::internals::context::Ctxt;

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
