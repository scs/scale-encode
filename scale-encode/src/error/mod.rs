//! An error that is emitted whenever some encoding fails.
mod context;
mod linkedlist;

use std::fmt::Display;
use std::borrow::Cow;

pub use context::{ Context, Location };

/// An error produced while attempting to encode some type.
#[derive(Debug, thiserror::Error)]
pub struct Error {
    context: Context,
    kind: ErrorKind,
}

impl Error {
    /// construct a new error given some context and an error kind.
    pub fn new(kind: ErrorKind) -> Error {
        Error {
            context: Context::new(),
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
    /// Give some context to the error.
    pub fn at(self, loc: Location) -> Self {
        Error {
            context: self.context.at(loc),
            kind: self.kind
        }
    }
    /// Note which sequence index the error occurred in.
    pub fn at_idx(self, idx: usize) -> Self {
        Error {
            context: self.context.at(Location::idx(idx)),
            kind: self.kind
        }
    }
    /// Note which field the error occurred in.
    pub fn at_field(self, field: impl Into<Cow<'static, str>>) -> Self {
        Error {
            context: self.context.at(Location::field(field)),
            kind: self.kind
        }
    }
    /// Note which variant the error occurred in.
    pub fn at_variant(self, variant: impl Into<Cow<'static, str>>) -> Self {
        Error {
            context: self.context.at(Location::variant(variant)),
            kind: self.kind
        }
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
#[derive(Debug, thiserror::Error)]
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
    /// Cannot find a field on our source type that's needed for the target type.
    #[error("Field {name} does not exist in our source struct")]
    CannotFindField {
        /// Name of the field which was not provided.
        name: String
    },
    /// A custom error.
    #[error("Custom error: {0}")]
    Custom(Box<dyn std::error::Error + Send + Sync + 'static>)
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