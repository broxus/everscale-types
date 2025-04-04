use proc_macro2::Ident;
use quote::{format_ident, ToTokens};
use syn::{Attribute, Error, LitStr, Path};

use crate::internals::context::Ctxt;

#[derive(Default)]
pub struct WithHandlers {
    pub abi_type_handler: Option<Path>,
    pub into_abi_handler: Option<Path>,
    pub from_abi_handler: Option<Path>,
}

pub struct FieldAttributes {
    pub extracted: bool,
    pub custom_name: Option<Ident>,
    pub mod_handler: Option<Path>,
    pub with_handlers: WithHandlers,
}

impl FieldAttributes {
    pub fn check(&self) -> Result<(), Error> {
        if let Some(path) = &self.mod_handler {
            if self.with_handlers.into_abi_handler.is_some()
                && self.with_handlers.from_abi_handler.is_some()
                && self.with_handlers.abi_type_handler.is_some()
            {
                return Err(Error::new_spanned(
                    path.into_token_stream(),
                    "`with` parameter should not be used simultaneously with other 3 handling parameters",
                ));
            }
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

pub fn extract_field_attributes(ctx: &Ctxt, attrs: &[Attribute]) -> FieldAttributes {
    let mut attributes = FieldAttributes {
        extracted: true,
        custom_name: None,
        mod_handler: None,
        with_handlers: Default::default(),
    };

    fn parse_path(value: syn::parse::ParseStream) -> Result<Path, Error> {
        let path_str: syn::LitStr = value.parse()?;
        let path = syn::parse_str::<Path>(&path_str.value())?;
        Ok(path)
    }

    for attr in attrs {
        if !attr.path().is_ident(ABI) {
            continue;
        }

        let result = attr.parse_nested_meta(|meta| {
            let value = meta.value()?;

            match &meta.path {
                path if path.is_ident(NAME) => {
                    if attributes.custom_name.is_some() {
                        attributes.extracted = false;
                        ctx.error_spanned_by(
                            path,
                            format!("Another {NAME} parameter already defined"),
                        );
                    }
                    match value.parse::<LitStr>() {
                        Ok(lit) => {
                            attributes.custom_name =
                                Some(format_ident!("{}", lit.value(), span = lit.span()));
                        }
                        Err(e) => {
                            attributes.extracted = false;
                            ctx.syn_error(e);
                        }
                    }
                }
                path if path.is_ident(WITH) => {
                    if attributes.mod_handler.is_some() {
                        attributes.extracted = false;
                        ctx.error_spanned_by(
                            path,
                            format!("Another {WITH} parameter already defined"),
                        );
                    }

                    match parse_path(value) {
                        Ok(path) => attributes.mod_handler = Some(path),
                        Err(e) => {
                            attributes.extracted = false;
                            ctx.syn_error(e);
                        }
                    }
                }
                path if path.is_ident(ABI_TYPE_WITH) => {
                    if attributes.with_handlers.abi_type_handler.is_some() {
                        attributes.extracted = false;
                        ctx.error_spanned_by(
                            path,
                            format!("Another {ABI_TYPE_WITH} parameter already defined"),
                        );
                    }

                    match parse_path(value) {
                        Ok(path) => attributes.with_handlers.abi_type_handler = Some(path),
                        Err(e) => {
                            attributes.extracted = false;
                            ctx.syn_error(e);
                        }
                    }
                }
                path if path.is_ident(INTO_ABI_WITH) => {
                    if attributes.with_handlers.into_abi_handler.is_some() {
                        attributes.extracted = false;
                        ctx.error_spanned_by(
                            path,
                            format!("Another {INTO_ABI_WITH} parameter already defined"),
                        );
                    }
                    match parse_path(value) {
                        Ok(path) => attributes.with_handlers.into_abi_handler = Some(path),
                        Err(e) => {
                            attributes.extracted = false;
                            ctx.syn_error(e);
                        }
                    }
                }
                path if path.is_ident(FROM_ABI_WITH) => {
                    if attributes.with_handlers.from_abi_handler.is_some() {
                        attributes.extracted = false;
                        ctx.error_spanned_by(
                            path,
                            format!("Another {FROM_ABI_WITH} parameter already defined"),
                        );
                    }

                    match parse_path(value) {
                        Ok(path) => attributes.with_handlers.from_abi_handler = Some(path),
                        Err(e) => {
                            attributes.extracted = false;
                            ctx.syn_error(e);
                        }
                    }
                }

                path => ctx.error_spanned_by(path, "Parameter is not supported"),
            }

            Ok(())
        });

        if let Err(e) = result {
            attributes.extracted = false;
            ctx.syn_error(e);
        }

        if let Err(e) = attributes.check() {
            attributes.extracted = false;
            ctx.syn_error(e);
        }
    }

    attributes
}
