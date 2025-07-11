use std::collections::HashSet;

use syn::punctuated::Pair;
use syn::visit::Visit;
use syn::{DataStruct, Fields, visit};

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
                ctx.error_spanned_by(input, "FromAbi doesn't support derive for enums");
                return None;
            }
            syn::Data::Union(_) => {
                ctx.error_spanned_by(input, "FromAbi doesn't support derive for unions");
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

pub fn with_bound(fields: &Fields, generics: &syn::Generics, bound: &syn::Path) -> syn::Generics {
    struct FindTyParams<'ast> {
        all_type_params: HashSet<syn::Ident>,
        relevant_type_params: HashSet<syn::Ident>,
        associated_type_usage: Vec<&'ast syn::TypePath>,
    }

    impl<'ast> Visit<'ast> for FindTyParams<'ast> {
        fn visit_field(&mut self, field: &'ast syn::Field) {
            if let syn::Type::Path(ty) = ungroup(&field.ty) {
                if let Some(Pair::Punctuated(t, _)) = ty.path.segments.pairs().next() {
                    if self.all_type_params.contains(&t.ident) {
                        self.associated_type_usage.push(ty);
                    }
                }
            }
            self.visit_type(&field.ty);
        }

        fn visit_macro(&mut self, _mac: &'ast syn::Macro) {}

        fn visit_path(&mut self, path: &'ast syn::Path) {
            if let Some(seg) = path.segments.last() {
                if seg.ident == "PhantomData" {
                    return;
                }
            }
            if path.leading_colon.is_none() && path.segments.len() == 1 {
                let id = &path.segments[0].ident;
                if self.all_type_params.contains(id) {
                    self.relevant_type_params.insert(id.clone());
                }
            }
            visit::visit_path(self, path);
        }
    }

    let all_type_params = generics
        .type_params()
        .map(|param| param.ident.clone())
        .collect();

    let mut visitor = FindTyParams {
        all_type_params,
        relevant_type_params: HashSet::new(),
        associated_type_usage: Vec::new(),
    };

    for field in fields.iter() {
        visitor.visit_field(field);
    }

    let relevant_type_params = visitor.relevant_type_params;
    let associated_type_params = visitor.associated_type_usage;

    let new_predicates = generics
        .type_params()
        .map(|param| param.ident.clone())
        .filter(|ident| relevant_type_params.contains(ident))
        .map(|ident| syn::TypePath {
            qself: None,
            path: ident.into(),
        })
        .chain(associated_type_params.into_iter().cloned())
        .map(|bounded_ty| {
            syn::WherePredicate::Type(syn::PredicateType {
                lifetimes: None,
                bounded_ty: syn::Type::Path(bounded_ty),
                colon_token: <syn::Token![:]>::default(),
                bounds: vec![syn::TypeParamBound::Trait(syn::TraitBound {
                    paren_token: None,
                    modifier: syn::TraitBoundModifier::None,
                    lifetimes: None,
                    path: bound.clone(),
                })]
                .into_iter()
                .collect(),
            })
        });

    let mut generics = generics.clone();
    generics
        .make_where_clause()
        .predicates
        .extend(new_predicates);
    generics
}

fn ungroup(mut ty: &syn::Type) -> &syn::Type {
    while let syn::Type::Group(group) = ty {
        ty = &group.elem;
    }
    ty
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
