use ahash::HashMap;
use anyhow::Result;
use sha2::Digest;

use crate::abi::value::ser::AbiSerializer;
use crate::abi::AbiHeader;
use crate::cell::{Cell, CellBuilder, CellSlice, DefaultFinalizer, Store};
use crate::models::{IntAddr, StdAddr};
use crate::num::Tokens;
use crate::prelude::HashBytes;

use super::error::AbiError;
use super::{AbiHeaderType, AbiValue, AbiVersion, NamedAbiType, NamedAbiValue, ShortAbiTypeSize};

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

    pub fn encode_internal_msg_body(
        version: AbiVersion,
        id: u32,
        tokens: &[NamedAbiValue],
    ) -> Result<CellBuilder> {
        let mut serializer = AbiSerializer::new(version);
        let output_id = AbiValue::uint(32, id);

        serializer.reserve_value(&output_id);
        for token in tokens {
            serializer.reserve_value(&token.value);
        }

        let finalizer = &mut Cell::default_finalizer();
        serializer.write_value(&output_id, finalizer)?;
        serializer.write_tuple(tokens, finalizer)?;
        serializer.finalize(finalizer).map_err(From::from)
    }

    pub fn encode_external_input(
        &self,
        tokens: &[NamedAbiValue],
        now: u64,
        expire_at: u32,
        key: Option<(&ed25519_dalek::SecretKey, Option<i32>)>,
        address: Option<&StdAddr>,
    ) -> Result<(CellBuilder, HashBytes)> {
        ok!(NamedAbiValue::check_types(tokens, &self.inputs));

        let mut serializer = AbiSerializer::new(self.abi_version);
        serializer.add_offset(if self.abi_version.major == 1 {
            // Reserve reference for signature
            ShortAbiTypeSize { bits: 0, refs: 1 }
        } else if key.is_some() {
            let bits = if self.abi_version >= AbiVersion::V2_3 {
                // Reserve only for address as it also ensures the the signature will fit
                IntAddr::BITS_MAX
            } else {
                // Reserve for `Some` non-empty signature
                1 + 512
            };
            ShortAbiTypeSize { bits, refs: 0 }
        } else {
            // Reserve for `None`
            ShortAbiTypeSize { bits: 1, refs: 0 }
        });

        let signing_key = key.map(|(key, signature_id)| {
            (Box::new(ed25519_dalek::SigningKey::from(key)), signature_id)
        });

        serializer.reserve_headers(&self.header, key.is_some());
        for token in tokens {
            serializer.reserve_value(&token.value);
        }

        for header in &self.header {
            serializer.write_header_value(&match header {
                AbiHeaderType::Time => AbiHeader::Time(now),
                AbiHeaderType::Expire => AbiHeader::Expire(expire_at),
                AbiHeaderType::PublicKey => AbiHeader::PublicKey(
                    signing_key
                        .as_ref()
                        .map(|(key, _)| Box::new(ed25519_dalek::VerifyingKey::from(key.as_ref()))),
                ),
            })?;
        }

        let finalizer = &mut Cell::default_finalizer();
        serializer.write_tuple(&tokens, finalizer)?;
        let builder = serializer.finalize(finalizer)?;

        let hash = if self.abi_version >= AbiVersion::V2_3 {
            let mut to_sign = CellBuilder::new();
            match address {
                Some(address) => address.store_into(&mut to_sign, finalizer)?,
                None => anyhow::bail!(AbiError::AddressNotProvided),
            };
            to_sign.store_builder(&builder)?;
            *to_sign.build_ext(finalizer)?.repr_hash()
        } else {
            *builder.clone().build_ext(finalizer)?.repr_hash()
        };

        Ok((builder, hash))
    }

    pub fn encode_internal_input(&self, tokens: &[NamedAbiValue]) -> Result<CellBuilder> {
        ok!(NamedAbiValue::check_types(tokens, &self.inputs));
        Self::encode_internal_msg_body(self.abi_version, self.input_id, tokens)
    }

    pub fn encode_internal_message(
        &self,
        tokens: &[NamedAbiValue],
        dst: IntAddr,
        value: Tokens,
    ) -> Result<Cell> {
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

    pub fn encode_output(&self, tokens: &[NamedAbiValue]) -> Result<CellBuilder> {
        ok!(NamedAbiValue::check_types(tokens, &self.outputs));
        Self::encode_internal_msg_body(self.abi_version, self.output_id, tokens)
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
