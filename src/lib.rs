//! `scale-encode` builds on `parity-scale-codec`. `parity-scale-codec` provides an `Encode` trait
//! which allows types to SCALE encode themselves with no external information. `scale-encode` provides an
//! [`EncodeAsType`] trait which allows types to decide how to encode themselves based on the desired
//! target type.
#![deny(missing_docs)]

mod impls;
mod context;
mod linkedlist;


use std::fmt::Display;
use scale_info::PortableRegistry;

pub use context::Context;

/// This trait signals that some static type can possibly be SCALE encoded given some
/// `type_id` and [`PortableRegistry`] which dictates the expected encoding. A [`Context`]
/// is also passed around, which is used internally to improve error reporting. Implementations
/// should use the [`Context::at`] method to indicate the current location if they would like
/// it to show up in error output.
pub trait EncodeAsType {
    /// This is a helper function which internally calls [`EncodeAsType::encode_as_type_to`]. Prefer to
    /// implement that instead.
    fn encode_as_type(&self, type_id: u32, types: &PortableRegistry, context: Context) -> Result<Vec<u8>, Error> {
        let mut out = Vec::new();
        self.encode_as_type_to(type_id, types, context, &mut out)?;
        Ok(out)
    }

    /// Given some `type_id`, `types`, a `context` and some output target for the SCALE encoded bytes,
    /// attempt to SCALE encode the current value into the type given by `type_id`.
    fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error>;
}

/// An error produced while attempting to encode some type.
#[derive(Debug, Clone, thiserror::Error)]
pub struct Error {
    context: Context,
    kind: ErrorKind,
}

impl Error {
    /// construct a new error given some context and an error kind.
    pub fn new(context: Context, kind: ErrorKind) -> Error {
        Error {
            context,
            kind
        }
    }
    /// Retrieve more information abotu what went wrong.
    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }
    /// Retrieve details about where the error occurred.
    pub fn context(&self) -> &Context {
        &self.context
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let path = self.context.path();
        let kind = &self.kind;
        write!(f, "Error at {path}: {kind}")
    }
}

/// The underlying nature of the error.
#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum ErrorKind {
    /// Cannot find a given type.
	#[error("Cannot find type with ID {0}")]
    TypeNotFound(u32),
    /// Cannot encode the actual type given into the target type ID.
	#[error("Cannot encode {actual:?} into type with ID {expected}")]
    WrongShape {
        /// The actual kind we have to encode
        actual: Kind,
        /// ID of the expected type.
        expected: u32
    },
    /// The types line up, but the expected length of the target type is different from the length of the input value.
	#[error("Cannot encode to ID {expected}; expected length {expected_len} but got length {actual_len}")]
    WrongLength {
        /// Length we have
        actual_len: usize,
        /// Length expected for type.
        expected_len: usize,
        /// ID of the expected type.
        expected: u32
    },
    /// We cannot encode the number given into the target type; it's out of range.
    #[error("Number {value} is out of range for target type {expected}")]
    NumberOutOfRange {
        /// A string represenatation of the numeric value that was out of range.
        value: String,
        /// Id of the expected numeric type that we tried to encode it to.
        expected: u32,
    },
    /// Cannot find a variant with a matching name on the target type.
    #[error("Variant {name} does not exist on type with ID {expected}")]
    CannotFindVariant {
        /// Variant name we can't find in the expected type.
        name: String,
        /// ID of the expected type.
        expected: u32
    },
}

/// The kind of type that we're trying to encode.
#[allow(missing_docs)]
#[derive(Copy,Clone,PartialEq,Eq,Debug)]
pub enum Kind {
    Struct,
    Tuple,
    Variant,
    Array,
    BitSequence,
    Bool,
    Char,
    Str,
    Number,
}

// TODO:
// - tests for current impls to verify against parity-scale-codec.
// - add derive crate to handle structs and variants. (make possible to impl for existing structs/enums in other crates too)