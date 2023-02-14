// Copyright (C) 2023 Parity Technologies (UK) Ltd. (admin@parity.io)
// This file is a part of the scale-encode crate.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//         http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! `scale-encode` builds on `parity-scale-codec`. `parity-scale-codec` provides an `Encode` trait
//! which allows types to SCALE encode themselves with no external information. `scale-encode` provides an
//! [`EncodeAsType`] trait which allows types to decide how to encode themselves based on the desired
//! target type.
#![deny(missing_docs)]

mod impls;

pub mod error;

pub use error::Error;
use scale_info::PortableRegistry;

/// Some utility types that are useful in order to help implement `EncodeAsType`.
pub mod utils {
    pub use crate::impls::{Composite, Variant};
    pub use scale_info::PortableRegistry;
}

#[cfg(feature = "derive")]
pub use scale_encode_derive::EncodeAsType;

/// This trait signals that some static type can possibly be SCALE encoded given some
/// `type_id` and [`PortableRegistry`] which dictates the expected encoding. A [`Context`]
/// is also passed around, which is used internally to improve error reporting. Implementations
/// should use the [`Context::at`] method to indicate the current location if they would like
/// it to show up in error output.
pub trait EncodeAsType {
    /// This is a helper function which internally calls [`EncodeAsType::encode_as_type_to`]. Prefer to
    /// implement that instead.
    fn encode_as_type(&self, type_id: u32, types: &PortableRegistry) -> Result<Vec<u8>, Error> {
        let mut out = Vec::new();
        self.encode_as_type_to(type_id, types, &mut out)?;
        Ok(out)
    }

    /// Given some `type_id`, `types`, a `context` and some output target for the SCALE encoded bytes,
    /// attempt to SCALE encode the current value into the type given by `type_id`.
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error>;
}
