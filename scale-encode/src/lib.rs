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

// Useful types to help implement EncodeAsType/Fields with:
pub use crate::impls::{Composite, Variant};
pub use scale_info::PortableRegistry;

/// A description of a single field in a tuple or struct type.
pub type PortableField = scale_info::Field<scale_info::form::PortableForm>;
/// A type ID used to represent tuple fields.
pub type PortableFieldId = scale_info::interner::UntrackedSymbol<std::any::TypeId>;

#[cfg(feature = "derive")]
pub use scale_encode_derive::EncodeAsType;

/// This trait signals that some static type can possibly be SCALE encoded given some
/// `type_id` and [`PortableRegistry`] which dictates the expected encoding.
pub trait EncodeAsType {
    /// Given some `type_id`, `types`, a `context` and some output target for the SCALE encoded bytes,
    /// attempt to SCALE encode the current value into the type given by `type_id`.
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error>;

    /// This is a helper function which internally calls [`EncodeAsType::encode_as_type_to`]. Prefer to
    /// implement that instead.
    fn encode_as_type(&self, type_id: u32, types: &PortableRegistry) -> Result<Vec<u8>, Error> {
        let mut out = Vec::new();
        self.encode_as_type_to(type_id, types, &mut out)?;
        Ok(out)
    }
}

/// This is similar to [`EncodeAsType`], except that it's can be implemented on types that can be encoded
/// to bytes given a list of fields instead of a single type ID. This is generally implemented just for
/// tuple and struct types, and is automatically implemented via the [`macro@EncodeAsType`] macro.
pub trait EncodeAsFields {
    /// Given some fields describing the shape of a type, attempt to encode to that shape.
    fn encode_as_fields_to(
        &self,
        fields: &[PortableField],
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error>;

    /// This is a helper function which internally calls [`EncodeAsFields::encode_as_fields_to`]. Prefer to
    /// implement that instead.
    fn encode_as_fields(
        &self,
        fields: &[PortableField],
        types: &PortableRegistry,
    ) -> Result<Vec<u8>, Error> {
        let mut out = Vec::new();
        self.encode_as_fields_to(fields, types, &mut out)?;
        Ok(out)
    }

    /// Given some field IDs describing the shape of a type, attempt to encode to that shape.
    fn encode_as_field_ids_to(
        &self,
        field_ids: &[PortableFieldId],
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        // [TODO jsdw]: It would be good to use a more efficient data structure
        // here to avoid allocating with smaller numbers of fields.
        let fields: Vec<PortableField> = field_ids
            .iter()
            .map(|f| PortableField::new(None, *f, None, Vec::new()))
            .collect();
        self.encode_as_fields_to(&fields, types, out)
    }

    /// This is a helper function which internally calls [`EncodeAsFields::encode_as_field_ids_to`]. Prefer to
    /// implement that instead.
    fn encode_as_field_ids(
        &self,
        field_ids: &[PortableFieldId],
        types: &PortableRegistry,
    ) -> Result<Vec<u8>, Error> {
        let mut out = Vec::new();
        self.encode_as_field_ids_to(field_ids, types, &mut out)?;
        Ok(out)
    }
}
