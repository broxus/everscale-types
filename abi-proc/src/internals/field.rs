use quote::format_ident;
use syn::Ident;

pub struct StructField {
    pub field_name: syn::Member,
    pub name_ident: Ident,
}

impl StructField {
    pub fn named(name: &syn::Ident) -> Self {
        Self {
            field_name: syn::Member::Named(name.clone()),
            name_ident: name.clone(),
        }
    }

    pub fn unnamed(field_index: usize) -> Self {
        Self {
            field_name: syn::Member::Unnamed(syn::Index::from(field_index)),
            name_ident: format_ident!("field_{field_index}"),
        }
    }
}
