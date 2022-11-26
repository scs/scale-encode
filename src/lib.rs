//! `scale-encode` builds on `parity-scale-codec`. `parity-scale-codec` provides an `Encode` trait
//! which allows types to SCALE encode themselves with no external information. `scale-encode` provides an
//! [`EncodeAsType`] trait which allows types to decide how to encode themselves based on the desired
//! target type.
#![deny(missing_docs)]

mod impls;
mod linkedlist;

pub mod context;
pub mod error;

use scale_info::PortableRegistry;

pub use context::Context;
pub use error::Error;

// These are exposed to be used in the proc macro crate and aren't part of the public interface.
#[doc(hidden)]
pub use impls::{
    Composite,
    Variant
};

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
