use proc_macro2::Ident;
use quote::format_ident;
use syn::{Attribute, LitStr, Path};

pub struct FieldAttributes {
    pub custom_name: Option<Ident>,
    pub custom_handler: Option<Path>,
}

pub fn extract_field_attributes(attrs: &[Attribute]) -> FieldAttributes {
    let mut attributes = FieldAttributes {
        custom_name: None,
        custom_handler: None,
    };
    for attr in attrs {
        if !attr.path().is_ident("abi") {
            continue;
        }
        let _ = attr.parse_nested_meta(|meta| {
            if meta.path.is_ident("name") {
                let value = meta.value()?;
                let lit: LitStr = value.parse()?;
                attributes.custom_name = Some(format_ident!("{}", lit.value(), span = lit.span()));
            } else if meta.path.is_ident("with") {
                let value = meta.value()?;
                let path_str: syn::LitStr = value.parse()?;
                let path = syn::parse_str::<Path>(&path_str.value())?;
                attributes.custom_handler = Some(path);
            }
            Ok(())
        });
    }

    attributes
}
