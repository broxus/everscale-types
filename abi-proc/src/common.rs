use proc_macro2::{Ident, Span};
use quote::format_ident;
use syn::spanned::Spanned;
use syn::{Attribute, Error, LitStr, Path};

pub enum HandlerType {
    AbiType,
    IntoAbi,
    FromAbi,
}

pub struct FieldAttributes {
    pub custom_name: Option<Ident>,
    pub mod_handler: Option<Path>,
    pub with_handlers: Vec<(HandlerType, Path)>,
}

impl FieldAttributes {
    pub fn check(&self) -> Result<(), Error> {
        if !self.with_handlers.is_empty() && self.mod_handler.is_some() {
            return Err(Error::new(
                Span::call_site(),
                "`with` attribute should not be used with other handling attributes",
            ));
        }
        Ok(())
    }
}

const ABI: &str = "abi";
const NAME: &str = "name";
const WITH: &str = "with";
const ABI_TYPE_WITH: &str = "abi_type_with";
const INTO_ABI_WITH: &str = "into_abi_with";
const FROM_ABI_WITH: &str = "from_abi_with";

pub fn extract_field_attributes(attrs: &[Attribute]) -> Result<FieldAttributes, Error> {
    let mut attributes = FieldAttributes {
        custom_name: None,
        mod_handler: None,
        with_handlers: Vec::new(),
    };

    fn parse_path(meta: syn::meta::ParseNestedMeta) -> Result<Path, Error> {
        let value = meta.value()?;
        let path_str: syn::LitStr = value.parse()?;
        let path = syn::parse_str::<Path>(&path_str.value())?;
        Ok(path)
    }

    for attr in attrs {
        if !attr.path().is_ident(ABI) {
            continue;
        }
        attr.parse_nested_meta(|meta| {
            match &meta.path {
                path if path.is_ident(NAME) => {
                    let value = meta.value()?;
                    let lit: LitStr = value.parse()?;
                    attributes.custom_name =
                        Some(format_ident!("{}", lit.value(), span = lit.span()));
                }
                path if path.is_ident(WITH) => {
                    let value = meta.value()?;
                    let path_str: syn::LitStr = value.parse()?;
                    let path = syn::parse_str::<Path>(&path_str.value())?;
                    attributes.mod_handler = Some(path);
                }
                path if path.is_ident(ABI_TYPE_WITH) => {
                    let path = parse_path(meta)?;
                    attributes.with_handlers.push((HandlerType::AbiType, path));
                }
                path if path.is_ident(INTO_ABI_WITH) => {
                    let path = parse_path(meta)?;
                    attributes.with_handlers.push((HandlerType::IntoAbi, path));
                }
                path if path.is_ident(FROM_ABI_WITH) => {
                    let path = parse_path(meta)?;
                    attributes.with_handlers.push((HandlerType::FromAbi, path));
                }

                path => {
                    let path = path.get_ident().map(|x| x.to_string()).unwrap_or_default();
                    return Err(Error::new(
                        attr.span(),
                        format!("Parameter {path} is not supported"),
                    ));
                }
            }

            Ok(())
        })?;
    }

    Ok(attributes)
}
