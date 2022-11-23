mod impls;

use std::fmt::Display;
use scale_info::PortableRegistry;

/// This trait signals that some static type can possibly be SCALE encoded, given some
/// `type_id` and [`PortableRegistry`] which dictates the expected encoding. A [`Context`]
/// is also passed around, which is used internally for
pub trait EncodeAsType {
    fn encode_as_type(&self, type_id: u32, types: &PortableRegistry, context: Context) -> Result<Vec<u8>, Error> {
        let mut out = Vec::new();
        self.encode_as_type_to(type_id, types, context, &mut out)?;
        Ok(out)
    }

    fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error>;
}

#[derive(Clone, Default)]
pub struct Context {
    path: Vec<Location>
}

impl Context {
    /// Construct a new, empty context.
    pub fn new() -> Context {
        Default::default()
    }
    #[doc(hidden)]
    pub fn push_field(&mut self, field: String) {
        self.path.push(Location::Field(field))
    }
    #[doc(hidden)]
    pub fn push_idx(&mut self, idx: usize) {
        self.path.push(Location::Index(idx))
    }
    #[doc(hidden)]
    pub fn push_variant(&mut self, name: String) {
        self.path.push(Location::Variant(name))
    }
    #[doc(hidden)]
    pub fn pop(&mut self) {
        self.path.pop();
    }
}

impl <'a> From<&'a Context> for Context {
    fn from(val: &'a Context) -> Self {
        val.clone()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub (crate) enum Location {
    Field(String),
    Index(usize),
    Variant(String)
}

#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub struct Error {
    path: Vec<Location>,
    kind: ErrorKind,
}

impl Error {
    pub fn new(context: impl Into<Context>, kind: ErrorKind) -> Error {
        Error {
            // Normally we'd want to accept an owned Context, but we accept
            // a borrowed one for generally better ergonomics and accept the cost
            // or a single clone for some eventual error if needed.
            path: context.into().path,
            kind
        }
    }
    pub fn kind(&self) -> &ErrorKind {
        &self.kind
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Error at ")?;

        // Print a path to the error:
        for (idx, loc) in self.path.iter().enumerate() {
            if idx != 0 {
                f.write_str(".")?;
            }
            match loc {
                Location::Field(name) => f.write_str(name)?,
                Location::Index(i) => write!(f, "[{i}]")?,
                Location::Variant(name) => write!(f, "({name})")?
            }
        }

        // Now print the actual error information:
        let kind = &self.kind;
        write!(f, ": {kind}")
    }
}

#[derive(Debug, Clone, thiserror::Error, PartialEq, Eq)]
pub enum ErrorKind {
	#[error("Cannot find type with ID {0}")]
    TypeNotFound(u32),
	#[error("Cannot encode {actual:?} into type with ID {expected}")]
    WrongShape {
        /// The actual kind we have to encode
        actual: Kind,
        /// ID of the expected type.
        expected: u32
    },
	#[error("Cannot encode to ID {expected}; expected length {expected_len} but got length {actual_len}")]
    WrongLength {
        /// Length we have
        actual_len: usize,
        /// Length expected for type.
        expected_len: usize,
        /// ID of the expected type.
        expected: u32
    },
    #[error("Number {value} is out of range for target type {target_type:?}")]
    NumberOutOfRange {
        value: String,
        target_type: NumericKind
    },
    #[error("Variant {name} does not exist on type with ID {expected}")]
    CannotFindVariant {
        /// Variant name we can't find in the expected type.
        name: String,
        /// ID of the expected type.
        expected: u32
    },
    #[error("Cannot encode value: {0}")]
    Codec(#[from] codec::Error),
    #[error("Cannot encode to the requested type with ID {id}: {reason}")]
    CannotEncodeToType {
        /// ID of the target type
        id: u32,
        /// Reason we cannot encode to this target type.
        reason: &'static str
    }
}

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

#[derive(Copy,Clone,PartialEq,Eq,Debug)]
pub enum NumericKind {
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
}

// TODO:
// - move Context and relaetd to a separate file. make linkedlist; need to be able to clone efficiently.
// - tests for current impls to verify against parity-scale-codec.
// - add derive crate to handle structs and variants.
// - consider adding EncodeAsTypeLike (which can hand back reference or actual type) and test.