use ahash::HashMap;
use anyhow::Result;
use sha2::Digest;

use crate::abi::value::ser::AbiSerializer;
use crate::abi::AbiHeader;
use crate::cell::{Cell, CellBuilder, CellSlice, DefaultFinalizer, Store};
use crate::models::{
    ExtInMsgInfo, IntAddr, MsgInfo, OwnedMessage, OwnedRelaxedMessage, RelaxedIntMsgInfo,
    RelaxedMsgInfo, StateInit, StdAddr,
};
use crate::num::Tokens;
use crate::prelude::{CellFamily, CellSliceRange, HashBytes};

use super::error::AbiError;
use super::{AbiHeaderType, AbiValue, AbiVersion, NamedAbiType, NamedAbiValue, ShortAbiTypeSize};

/// Contract ABI definition.
pub struct Contract {
    /// ABI version.
    pub abi_version: AbiVersion,

    /// List of headers for external messages.
    ///
    /// NOTE: header order matters.
    pub header: Vec<AbiHeaderType>,

    /// A mapping with all contract methods by name.
    pub functions: HashMap<String, Function>,
}

/// Contract method ABI definition.
pub struct Function {
    /// ABI version (same as contract ABI version).
    pub abi_version: AbiVersion,

    /// List of headers for external messages.
    /// Must be the same as in contract.
    ///
    /// NOTE: header order matters.
    pub header: Vec<AbiHeaderType>,

    /// Method name.
    pub name: String,

    /// Method input argument types.
    pub inputs: Vec<NamedAbiType>,
    /// Method output types.
    pub outputs: Vec<NamedAbiType>,

    /// Function id in incoming messages (with input).
    pub input_id: u32,
    /// Function id in outgoing messages (with output).
    pub output_id: u32,
}

impl Function {
    /// Computes function id from the full function signature.
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

    /// Encodes message body without headers.
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

    /// Encodes an unsigned body with invocation of this method with as an external message.
    pub fn encode_external_input(
        &self,
        tokens: &[NamedAbiValue],
        now: u64,
        expire_at: u32,
        pubkey: Option<&ed25519_dalek::VerifyingKey>,
        address: Option<&StdAddr>,
    ) -> Result<UnsignedBody> {
        ok!(NamedAbiValue::check_types(tokens, &self.inputs));

        let mut serializer = AbiSerializer::new(self.abi_version);
        serializer.add_offset(if self.abi_version.major == 1 {
            // Reserve reference for signature
            ShortAbiTypeSize { bits: 0, refs: 1 }
        } else if pubkey.is_some() {
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

        serializer.reserve_headers(&self.header, pubkey.is_some());
        for token in tokens {
            serializer.reserve_value(&token.value);
        }

        for header in &self.header {
            serializer.write_header_value(&match header {
                AbiHeaderType::Time => AbiHeader::Time(now),
                AbiHeaderType::Expire => AbiHeader::Expire(expire_at),
                AbiHeaderType::PublicKey => AbiHeader::PublicKey(pubkey.map(|key| Box::new(*key))),
            })?;
        }

        let finalizer = &mut Cell::default_finalizer();
        serializer.write_tuple(tokens, finalizer)?;
        let builder = serializer.finalize(finalizer)?;

        let (hash, payload) = if self.abi_version >= AbiVersion::V2_3 {
            let mut to_sign = CellBuilder::new();
            match address {
                Some(address) => address.store_into(&mut to_sign, finalizer)?,
                None => anyhow::bail!(AbiError::AddressNotProvided),
            };
            to_sign.store_builder(&builder)?;
            let hash = *to_sign.build_ext(finalizer)?.repr_hash();
            (hash, builder.build()?)
        } else {
            let payload = builder.clone().build_ext(finalizer)?;
            (*payload.repr_hash(), payload)
        };

        Ok(UnsignedBody {
            abi_version: self.abi_version,
            expire_at,
            payload,
            hash,
        })
    }

    /// Encodes an unsigned external message with invocation of this method.
    pub fn encode_external_message(
        &self,
        tokens: &[NamedAbiValue],
        now: u64,
        expire_at: u32,
        pubkey: Option<&ed25519_dalek::VerifyingKey>,
        address: &StdAddr,
    ) -> Result<UnsignedExternalMessage> {
        Ok(self
            .encode_external_input(tokens, now, expire_at, pubkey, Some(address))?
            .with_dst(address.clone()))
    }

    /// Encodes a message body with invocation of this method with as an internal message.
    pub fn encode_internal_input(&self, tokens: &[NamedAbiValue]) -> Result<CellBuilder> {
        ok!(NamedAbiValue::check_types(tokens, &self.inputs));
        Self::encode_internal_msg_body(self.abi_version, self.input_id, tokens)
    }

    /// Encodes an internal message with invocation of this method.
    pub fn encode_internal_message(
        &self,
        tokens: &[NamedAbiValue],
        dst: IntAddr,
        value: Tokens,
        bounce: bool,
        state_init: Option<&StateInit>,
    ) -> Result<Box<OwnedRelaxedMessage>> {
        let body = self.encode_internal_input(tokens)?;
        let cell = body.build()?;
        let range = CellSliceRange::full(cell.as_ref());

        Ok(Box::new(OwnedRelaxedMessage {
            info: RelaxedMsgInfo::Int(RelaxedIntMsgInfo {
                dst,
                bounce,
                value: value.into(),
                ..Default::default()
            }),
            body: (cell, range),
            init: state_init.cloned(),
            layout: None,
        }))
    }

    /// Tries to parse input arguments for this method from an internal message body.
    ///
    /// NOTE: The slice is required to contain nothing other than these arguments.
    pub fn decode_internal_input(&self, mut slice: CellSlice<'_>) -> Result<Vec<NamedAbiValue>> {
        self.decode_internal_input_ext(&mut slice, false)
    }

    /// Tries to parse input arguments for this method from an internal message body.
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

    /// Encodes a message body with result of invocation of this method.
    pub fn encode_output(&self, tokens: &[NamedAbiValue]) -> Result<CellBuilder> {
        ok!(NamedAbiValue::check_types(tokens, &self.outputs));
        Self::encode_internal_msg_body(self.abi_version, self.output_id, tokens)
    }

    /// Tries to parse output arguments of this method from a message body.
    ///
    /// NOTE: The slice is required to contain nothing other than these arguments.
    pub fn decode_output(&self, mut slice: CellSlice<'_>) -> Result<Vec<NamedAbiValue>> {
        self.decode_output_ext(&mut slice, false)
    }

    /// Tries to parse output arguments of this method from a message body.
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

    /// Returns an object which can be used to display the normalized signature of this method.
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

/// Unsigned external message.
pub struct UnsignedExternalMessage {
    /// Destination contract address.
    pub dst: StdAddr,
    /// Unsigned payload.
    pub body: UnsignedBody,
    /// Optional initial contract state.
    pub init: Option<StateInit>,
}

impl UnsignedExternalMessage {
    /// Updates the state init of the external message to the specified one.
    pub fn set_state_init(&mut self, init: Option<StateInit>) {
        self.init = init;
    }

    /// Returns an external message with the specified state init.
    pub fn with_state_init(mut self, init: StateInit) -> Self {
        self.set_state_init(Some(init));
        self
    }

    /// Returns the expiration timestamp of this message.
    #[inline]
    pub fn expire_at(&self) -> u32 {
        self.body.expire_at
    }

    /// Signs the payload and returns an external message with filled signature.
    pub fn sign(
        self,
        key: &ed25519_dalek::SigningKey,
        signature_id: Option<i32>,
    ) -> Result<OwnedMessage> {
        let signature =
            crate::abi::sign_with_signature_id(key, self.body.hash.as_slice(), signature_id);
        self.with_signature(&signature)
    }

    /// Returns an external message with filled signature.
    pub fn with_signature(self, signature: &ed25519_dalek::Signature) -> Result<OwnedMessage> {
        self.into_signed(Some(&signature.to_bytes()))
    }

    /// Returns an external message with signature filled with zero bytes.
    pub fn with_fake_signature(self) -> Result<OwnedMessage> {
        self.into_signed(Some(&[0u8; 64]))
    }

    /// Returns an external message with empty signature.
    pub fn without_signature(self) -> Result<OwnedMessage> {
        self.into_signed(None)
    }

    /// Returns an external message with filled signature.
    pub fn fill_signature(&self, signature: Option<&[u8; 64]>) -> Result<OwnedMessage> {
        let body = self.body.fill_signature(signature)?;
        let range = CellSliceRange::full(body.as_ref());
        Ok(OwnedMessage {
            info: MsgInfo::ExtIn(ExtInMsgInfo {
                dst: IntAddr::Std(self.dst.clone()),
                ..Default::default()
            }),
            body: (body, range),
            init: self.init.clone(),
            layout: None,
        })
    }

    /// Converts an unsigned message into an external message with filled signature.
    fn into_signed(self, signature: Option<&[u8; 64]>) -> Result<OwnedMessage> {
        let body = self.body.fill_signature(signature)?;
        let range = CellSliceRange::full(body.as_ref());
        Ok(OwnedMessage {
            info: MsgInfo::ExtIn(ExtInMsgInfo {
                dst: IntAddr::Std(self.dst),
                ..Default::default()
            }),
            body: (body, range),
            init: self.init,
            layout: None,
        })
    }
}

/// Unsigned external message payload.
pub struct UnsignedBody {
    /// ABI version used during encoding.
    pub abi_version: AbiVersion,
    /// Unsigned payload.
    pub payload: Cell,
    /// A hash to sign.
    pub hash: HashBytes,
    /// Message expiration timestamp (in seconds).
    pub expire_at: u32,
}

impl UnsignedBody {
    /// Extends message with the specified destination address and returns an
    /// unsigned external message.
    pub fn with_dst(self, dst: StdAddr) -> UnsignedExternalMessage {
        UnsignedExternalMessage {
            dst,
            body: self,
            init: None,
        }
    }

    /// Signs the payload and returns a body cell with filled signature.
    pub fn sign(self, key: &ed25519_dalek::SigningKey, signature_id: Option<i32>) -> Result<Cell> {
        let signature = crate::abi::sign_with_signature_id(key, self.hash.as_slice(), signature_id);
        self.with_signature(&signature)
    }

    /// Returns a body cell with filled signature.
    pub fn with_signature(self, signature: &ed25519_dalek::Signature) -> Result<Cell> {
        self.fill_signature(Some(&signature.to_bytes()))
    }

    /// Returns a body cell with signature filled with zero bytes.
    pub fn with_fake_signature(self) -> Result<Cell> {
        self.fill_signature(Some(&[0u8; 64]))
    }

    /// Returns a body cell with empty signature.
    pub fn without_signature(self) -> Result<Cell> {
        self.fill_signature(None)
    }

    /// Returns a body cell with filled signature.
    pub fn fill_signature(&self, signature: Option<&[u8; 64]>) -> Result<Cell> {
        let mut builder = CellBuilder::new();

        if self.abi_version.major == 1 {
            builder.store_reference(match signature {
                Some(signature) => {
                    // TODO: extend with public key?
                    CellBuilder::from_raw_data(signature, 512).and_then(CellBuilder::build)?
                }
                None => Cell::empty_cell(),
            })?;
        } else {
            match signature {
                Some(signature) => {
                    builder.store_bit_one()?;
                    builder.store_raw(signature, 512)?;
                }
                None => builder.store_bit_zero()?,
            }
            builder.store_slice(self.payload.as_slice()?)?;
        }

        builder.build().map_err(From::from)
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
