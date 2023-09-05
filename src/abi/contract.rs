use ahash::HashMap;
use anyhow::Result;
use sha2::Digest;

use crate::abi::AbiValue;
use crate::cell::{CellBuilder, CellSlice};

use super::error::AbiError;
use super::{AbiHeaderType, AbiVersion, NamedAbiType, NamedAbiValue};

pub struct Contract {
    pub abi_version: AbiVersion,
    pub header: Vec<AbiHeaderType>,
    pub functions: HashMap<String, Function>,
}

pub struct Function {
    pub abi_version: AbiVersion,
    pub header: Vec<AbiHeaderType>,
    pub name: String,
    pub inputs: Vec<NamedAbiType>,
    pub outputs: Vec<NamedAbiType>,
    pub input_id: u32,
    pub output_id: u32,
}

impl Function {
    pub fn compute_function_id(
        abi_version: AbiVersion,
        name: &str,
        header: &[AbiHeaderType],
        inputs: &[NamedAbiType],
        outputs: &[NamedAbiType],
    ) -> u32 {
        let mut hasher = sha2::Sha256::new();
        FunctionSignatureRaw {
            abi_version,
            name,
            header,
            inputs,
            outputs,
        }
        .update_hasher(&mut hasher);

        let hash: [u8; 32] = hasher.finalize().into();
        u32::from_be_bytes(hash[0..4].try_into().unwrap())
    }

    pub fn decode_internal_input(&self, mut slice: CellSlice<'_>) -> Result<Vec<NamedAbiValue>> {
        self.decode_internal_input_ext(&mut slice, false)
    }

    pub fn decode_internal_input_ext(
        &self,
        slice: &mut CellSlice<'_>,
        allow_partial: bool,
    ) -> Result<Vec<NamedAbiValue>> {
        let id = slice.load_u32()?;
        anyhow::ensure!(
            id == self.input_id,
            AbiError::InputIdMismatch {
                expected: self.input_id,
                id
            }
        );
        let res = ok!(NamedAbiValue::load_tuple_ext(
            &self.inputs,
            self.abi_version,
            true,
            allow_partial,
            slice
        ));
        ok!(AbiValue::check_remaining(slice, allow_partial));
        Ok(res)
    }

    pub fn decode_output(&self, mut slice: CellSlice<'_>) -> Result<Vec<NamedAbiValue>> {
        self.decode_output_ext(&mut slice, false)
    }

    pub fn decode_output_ext(
        &self,
        slice: &mut CellSlice<'_>,
        allow_partial: bool,
    ) -> Result<Vec<NamedAbiValue>> {
        let id = slice.load_u32()?;
        anyhow::ensure!(
            id == self.output_id,
            AbiError::OutputIdMismatch {
                expected: self.output_id,
                id
            }
        );
        let res = ok!(NamedAbiValue::load_tuple_ext(
            &self.outputs,
            self.abi_version,
            true,
            allow_partial,
            slice
        ));
        ok!(AbiValue::check_remaining(slice, allow_partial));
        Ok(res)
    }

    pub fn display_signature(&self) -> impl std::fmt::Display + '_ {
        FunctionSignatureRaw {
            abi_version: self.abi_version,
            name: &self.name,
            header: &self.header,
            inputs: &self.inputs,
            outputs: &self.outputs,
        }
    }
}

struct FunctionSignatureRaw<'a> {
    abi_version: AbiVersion,
    name: &'a str,
    header: &'a [AbiHeaderType],
    inputs: &'a [NamedAbiType],
    outputs: &'a [NamedAbiType],
}

impl FunctionSignatureRaw<'_> {
    fn update_hasher<H: Digest>(&self, engine: &mut H) {
        #[repr(transparent)]
        struct Hasher<'a, H>(&'a mut H);

        impl<H: Digest> std::fmt::Write for Hasher<'_, H> {
            #[inline]
            fn write_str(&mut self, s: &str) -> std::fmt::Result {
                self.0.update(s.as_bytes());
                Ok(())
            }
        }

        std::fmt::write(&mut Hasher(engine), format_args!("{self}")).unwrap();
    }
}

impl std::fmt::Display for FunctionSignatureRaw<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        ok!(write!(f, "{}(", self.name));

        let mut first = true;
        if self.abi_version.major == 1 {
            for header in self.header {
                if !std::mem::take(&mut first) {
                    ok!(f.write_str(","));
                }
                ok!(std::fmt::Display::fmt(header, f));
            }
        }
        for item in self.inputs {
            if !std::mem::take(&mut first) {
                ok!(f.write_str(","));
            }
            ok!(std::fmt::Display::fmt(&item.ty, f));
        }

        ok!(f.write_str(")("));

        first = true;
        for item in self.outputs {
            if !std::mem::take(&mut first) {
                ok!(f.write_str(","));
            }
            ok!(std::fmt::Display::fmt(&item.ty, f));
        }

        write!(f, ")v{}", self.abi_version.major)
    }
}
