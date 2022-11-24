//! An error that is emitted whenever some encoding fails.

use std::fmt::Display;
use crate::context::Context;

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