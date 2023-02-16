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

#[cfg(feature = "bits")]
mod bits;
mod composite;
#[cfg(feature = "primitive-types")]
mod primitive_types;
mod variant;

// Useful to help encode key-value types or custom variant types manually.
// Primarily used in the derive macro.
pub use composite::Composite;
pub use variant::Variant;

use crate::error::{Error, ErrorKind, Kind};
use crate::EncodeAsType;
use codec::{Compact, Encode};
use core::num::{
    NonZeroI128, NonZeroI16, NonZeroI32, NonZeroI64, NonZeroI8, NonZeroU128, NonZeroU16,
    NonZeroU32, NonZeroU64, NonZeroU8,
};
use core::ops::{Range, RangeInclusive};
use scale_info::{PortableRegistry, TypeDef, TypeDefPrimitive};
use std::collections::{BTreeMap, BTreeSet, BinaryHeap, LinkedList, VecDeque};
use std::marker::PhantomData;
use std::rc::Rc;
use std::sync::Arc;
use std::time::Duration;

impl EncodeAsType for bool {
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        let type_id = find_single_entry_with_same_repr(type_id, types);
        let ty = types
            .resolve(type_id)
            .ok_or_else(|| Error::new(ErrorKind::TypeNotFound(type_id)))?;

        if let TypeDef::Primitive(TypeDefPrimitive::Bool) = ty.type_def() {
            self.encode_to(out);
            Ok(())
        } else {
            Err(Error::new(ErrorKind::WrongShape {
                actual: Kind::Bool,
                expected: type_id,
            }))
        }
    }
}

impl EncodeAsType for str {
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        let type_id = find_single_entry_with_same_repr(type_id, types);
        let ty = types
            .resolve(type_id)
            .ok_or_else(|| Error::new(ErrorKind::TypeNotFound(type_id)))?;

        if let TypeDef::Primitive(TypeDefPrimitive::Str) = ty.type_def() {
            self.encode_to(out);
            Ok(())
        } else {
            Err(Error::new(ErrorKind::WrongShape {
                actual: Kind::Str,
                expected: type_id,
            }))
        }
    }
}

impl<'a, T> EncodeAsType for &'a T
where
    T: EncodeAsType + ?Sized,
{
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        (*self).encode_as_type_to(type_id, types, out)
    }
}

impl<'a, T> EncodeAsType for std::borrow::Cow<'a, T>
where
    T: 'a + EncodeAsType + ToOwned + ?Sized,
{
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        (**self).encode_as_type_to(type_id, types, out)
    }
}

impl<T> EncodeAsType for [T]
where
    T: EncodeAsType,
{
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        encode_iterable_sequence_to(self.len(), self.iter(), type_id, types, out)
    }
}

impl<const N: usize, T: EncodeAsType> EncodeAsType for [T; N] {
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        self[..].encode_as_type_to(type_id, types, out)
    }
}

impl<T> EncodeAsType for PhantomData<T> {
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        ().encode_as_type_to(type_id, types, out)
    }
}

impl<T: EncodeAsType, E: EncodeAsType> EncodeAsType for Result<T, E> {
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        match self {
            Ok(v) => Variant {
                name: "Ok",
                fields: Composite([(None, v as &dyn EncodeAsType)].iter().copied()),
            }
            .encode_as_type_to(type_id, types, out),
            Err(e) => Variant {
                name: "Err",
                fields: Composite([(None, e as &dyn EncodeAsType)].iter().copied()),
            }
            .encode_as_type_to(type_id, types, out),
        }
    }
}

impl<T: EncodeAsType> EncodeAsType for Option<T> {
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        match self {
            Some(v) => Variant {
                name: "Some",
                fields: Composite([(None, v as &dyn EncodeAsType)].iter().copied()),
            }
            .encode_as_type_to(type_id, types, out),
            None => Variant {
                name: "None",
                fields: Composite([].iter().copied()),
            }
            .encode_as_type_to(type_id, types, out),
        }
    }
}

// Encode any numeric type implementing ToNumber, above, into the type ID given.
macro_rules! impl_encode_number {
    ($ty:ty) => {
        impl EncodeAsType for $ty {
            fn encode_as_type_to(
                &self,
                type_id: u32,
                types: &PortableRegistry,
                out: &mut Vec<u8>,
            ) -> Result<(), Error> {
                let type_id = find_single_entry_with_same_repr(type_id, types);

                let ty = types
                    .resolve(type_id)
                    .ok_or_else(|| Error::new(ErrorKind::TypeNotFound(type_id)))?;

                fn try_num<T: TryFrom<$ty> + Encode>(
                    num: $ty,
                    target_id: u32,
                    out: &mut Vec<u8>,
                ) -> Result<(), Error> {
                    let n: T = num.try_into().map_err(|_| {
                        Error::new(ErrorKind::NumberOutOfRange {
                            value: num.to_string(),
                            expected: target_id,
                        })
                    })?;
                    n.encode_to(out);
                    Ok(())
                }

                match ty.type_def() {
                    TypeDef::Primitive(TypeDefPrimitive::U8) => try_num::<u8>(*self, type_id, out),
                    TypeDef::Primitive(TypeDefPrimitive::U16) => {
                        try_num::<u16>(*self, type_id, out)
                    }
                    TypeDef::Primitive(TypeDefPrimitive::U32) => {
                        try_num::<u32>(*self, type_id, out)
                    }
                    TypeDef::Primitive(TypeDefPrimitive::U64) => {
                        try_num::<u64>(*self, type_id, out)
                    }
                    TypeDef::Primitive(TypeDefPrimitive::U128) => {
                        try_num::<u128>(*self, type_id, out)
                    }
                    TypeDef::Primitive(TypeDefPrimitive::I8) => try_num::<i8>(*self, type_id, out),
                    TypeDef::Primitive(TypeDefPrimitive::I16) => {
                        try_num::<i16>(*self, type_id, out)
                    }
                    TypeDef::Primitive(TypeDefPrimitive::I32) => {
                        try_num::<i32>(*self, type_id, out)
                    }
                    TypeDef::Primitive(TypeDefPrimitive::I64) => {
                        try_num::<i64>(*self, type_id, out)
                    }
                    TypeDef::Primitive(TypeDefPrimitive::I128) => {
                        try_num::<i128>(*self, type_id, out)
                    }
                    TypeDef::Compact(c) => {
                        let type_id = find_single_entry_with_same_repr(c.type_param().id(), types);

                        let ty = types
                            .resolve(type_id)
                            .ok_or_else(|| Error::new(ErrorKind::TypeNotFound(type_id)))?;

                        macro_rules! try_compact_num {
                            ($num:expr, $target_kind:expr, $out:expr, $type:ty) => {{
                                let n: $type = $num.try_into().map_err(|_| {
                                    Error::new(ErrorKind::NumberOutOfRange {
                                        value: $num.to_string(),
                                        expected: type_id,
                                    })
                                })?;
                                Compact(n).encode_to($out);
                                Ok(())
                            }};
                        }

                        match ty.type_def() {
                            TypeDef::Primitive(TypeDefPrimitive::U8) => {
                                try_compact_num!(*self, NumericKind::U8, out, u8)
                            }
                            TypeDef::Primitive(TypeDefPrimitive::U16) => {
                                try_compact_num!(*self, NumericKind::U16, out, u16)
                            }
                            TypeDef::Primitive(TypeDefPrimitive::U32) => {
                                try_compact_num!(*self, NumericKind::U32, out, u32)
                            }
                            TypeDef::Primitive(TypeDefPrimitive::U64) => {
                                try_compact_num!(*self, NumericKind::U64, out, u64)
                            }
                            TypeDef::Primitive(TypeDefPrimitive::U128) => {
                                try_compact_num!(*self, NumericKind::U128, out, u128)
                            }
                            _ => Err(Error::new(ErrorKind::WrongShape {
                                actual: Kind::Number,
                                expected: type_id,
                            })),
                        }
                    }
                    _ => Err(Error::new(ErrorKind::WrongShape {
                        actual: Kind::Number,
                        expected: type_id,
                    })),
                }
            }
        }
    };
}
impl_encode_number!(u8);
impl_encode_number!(u16);
impl_encode_number!(u32);
impl_encode_number!(u64);
impl_encode_number!(u128);
impl_encode_number!(i8);
impl_encode_number!(i16);
impl_encode_number!(i32);
impl_encode_number!(i64);
impl_encode_number!(i128);

// Encode tuple types to any matching type.
macro_rules! impl_encode_tuple {
    ($($name:ident: $t:ident),*) => {
        impl < $($t),* > EncodeAsType for ($($t,)*) where $($t: EncodeAsType),* {
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, out: &mut Vec<u8>) -> Result<(), Error> {
                let ($($name,)*) = self;
                Composite([
                    $(
                        (None as Option<&'static str>, $name as &dyn EncodeAsType)
                    ,)*
                ].iter().copied()).encode_as_type_to(type_id, types, out)
            }
        }
    }
}
#[rustfmt::skip]
const _: () = {
    impl_encode_tuple!();
    impl_encode_tuple!(a: A);
    impl_encode_tuple!(a: A, b: B);
    impl_encode_tuple!(a: A, b: B, c: C);
    impl_encode_tuple!(a: A, b: B, c: C, d: D);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R);
    impl_encode_tuple!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S);
    // ^ Note: We make sure to support as many as parity-scale-codec's Encode impls do.
};

// Implement encoding via iterators for ordered collections
macro_rules! impl_encode_seq_via_iterator {
    ($ty:ident $( [$($param:ident),+] )?) => {
        impl $(< $($param),+ >)? EncodeAsType for $ty $(< $($param),+ >)?
        where $( $($param: EncodeAsType),+ )?
        {
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, out: &mut Vec<u8>) -> Result<(), Error> {
                encode_iterable_sequence_to(self.len(), self.iter(), type_id, types, out)
            }
        }
    }
}
impl_encode_seq_via_iterator!(BTreeSet[K]);
impl_encode_seq_via_iterator!(LinkedList[V]);
impl_encode_seq_via_iterator!(BinaryHeap[V]);
impl_encode_seq_via_iterator!(VecDeque[V]);
impl_encode_seq_via_iterator!(Vec[V]);

impl<K: AsRef<str>, V: EncodeAsType> EncodeAsType for BTreeMap<K, V> {
    fn encode_as_type_to(
        &self,
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error> {
        Composite(
            self.iter()
                .map(|(k, v)| (Some(k.as_ref()), v as &dyn EncodeAsType)),
        )
        .encode_as_type_to(type_id, types, out)
    }
}

// Generate EncodeAsType impls for simple types that can be easily transformed
// into types we have impls for already.
macro_rules! impl_encode_like {
    ($ty:ident $(<$( $param:ident ),+>)? as $delegate_ty:ty where |$val:ident| $expr:expr) => {
        impl $(< $($param: EncodeAsType),+ >)? EncodeAsType for $ty $(<$( $param ),+>)? {
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, out: &mut Vec<u8>) -> Result<(), Error> {
                let delegate: $delegate_ty = {
                    let $val = self;
                    $expr
                };
                delegate.encode_as_type_to(type_id, types, out)
            }
        }
    }
}
impl_encode_like!(String as &str where |val| val);
impl_encode_like!(Box<T> as &T where |val| val);
impl_encode_like!(Arc<T> as &T where |val| val);
impl_encode_like!(Rc<T> as &T where |val| val);
impl_encode_like!(char as u32 where |val| *val as u32);
impl_encode_like!(NonZeroU8 as u8 where |val| val.get());
impl_encode_like!(NonZeroU16 as u16 where |val| val.get());
impl_encode_like!(NonZeroU32 as u32 where |val| val.get());
impl_encode_like!(NonZeroU64 as u64 where |val| val.get());
impl_encode_like!(NonZeroU128 as u128 where |val| val.get());
impl_encode_like!(NonZeroI8 as i8 where |val| val.get());
impl_encode_like!(NonZeroI16 as i16 where |val| val.get());
impl_encode_like!(NonZeroI32 as i32 where |val| val.get());
impl_encode_like!(NonZeroI64 as i64 where |val| val.get());
impl_encode_like!(NonZeroI128 as i128 where |val| val.get());
impl_encode_like!(Duration as (u64, u32) where |val| (val.as_secs(), val.subsec_nanos()));
impl_encode_like!(Range<T> as (&T, &T) where |val| (&val.start, &val.end));
impl_encode_like!(RangeInclusive<T> as (&T, &T) where |val| ((val.start()), (val.end())));
impl_encode_like!(Compact<T> as &T where |val| &val.0);

// Attempt to recurse into some type, returning the innermost type found that has an identical
// SCALE encoded representation to the given type. For instance, `(T,)` encodes identically to
// `T`, as does `Mytype { inner: T }` or `[T; 1]`.
fn find_single_entry_with_same_repr(type_id: u32, types: &PortableRegistry) -> u32 {
    let Some(ty) = types.resolve(type_id) else {
        return type_id
    };
    match ty.type_def() {
        TypeDef::Tuple(tuple) if tuple.fields().len() == 1 => {
            find_single_entry_with_same_repr(tuple.fields()[0].id(), types)
        }
        TypeDef::Composite(composite) if composite.fields().len() == 1 => {
            find_single_entry_with_same_repr(composite.fields()[0].ty().id(), types)
        }
        _ => type_id,
    }
}

// Encode some iterator of items to the type provided.
fn encode_iterable_sequence_to<I>(
    len: usize,
    mut it: I,
    type_id: u32,
    types: &PortableRegistry,
    out: &mut Vec<u8>,
) -> Result<(), Error>
where
    I: Iterator,
    I::Item: EncodeAsType,
{
    let ty = types
        .resolve(type_id)
        .ok_or_else(|| Error::new(ErrorKind::TypeNotFound(type_id)))?;

    match ty.type_def() {
        TypeDef::Array(arr) => {
            if arr.len() == len as u32 {
                for (idx, item) in it.enumerate() {
                    item.encode_as_type_to(arr.type_param().id(), types, out)
                        .map_err(|e| e.at_idx(idx))?;
                }
                Ok(())
            } else {
                Err(Error::new(ErrorKind::WrongLength {
                    actual_len: len,
                    expected_len: arr.len() as usize,
                    expected: type_id,
                }))
            }
        }
        TypeDef::Sequence(seq) => {
            // Sequences are prefixed with their compact encoded length:
            Compact(len as u32).encode_to(out);
            for (idx, item) in it.enumerate() {
                item.encode_as_type_to(seq.type_param().id(), types, out)
                    .map_err(|e| e.at_idx(idx))?;
            }
            Ok(())
        }
        // if the target type is a basic newtype wrapper, then dig into that and try encoding to
        // the thing inside it. This is fairly common, and allowing this means that users don't have
        // to wrap things needlessly just to make types line up.
        TypeDef::Tuple(tup) if tup.fields().len() == 1 => {
            encode_iterable_sequence_to(len, it, tup.fields()[0].id(), types, out)
        }
        TypeDef::Composite(com) if com.fields().len() == 1 => {
            encode_iterable_sequence_to(len, it, com.fields()[0].ty().id(), types, out)
        }
        _ => {
            // As a last ditch attempt, if the sequence we're trying to encode has 1 value in,
            // then try encoding that value to the target type before giving up.
            let single_item = if len == 1 { it.next() } else { None };

            if let Some(item) = single_item {
                item.encode_as_type_to(type_id, types, out)
                    .map_err(|e| e.at_idx(0))?;
                Ok(())
            } else {
                Err(Error::new(ErrorKind::WrongShape {
                    actual: Kind::Array,
                    expected: type_id,
                }))
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use codec::Decode;
    use scale_info::TypeInfo;
    use std::fmt::Debug;

    /// Given a type definition, return type ID and registry representing it.
    fn make_type<T: TypeInfo + 'static>() -> (u32, PortableRegistry) {
        let m = scale_info::MetaType::new::<T>();
        let mut types = scale_info::Registry::new();
        let id = types.register_type(&m);
        let portable_registry: PortableRegistry = types.into();

        (id.id(), portable_registry)
    }

    fn encode_type<V: EncodeAsType, T: TypeInfo + 'static>(value: V) -> Result<Vec<u8>, Error> {
        let (type_id, types) = make_type::<T>();
        let bytes = value.encode_as_type(type_id, &types)?;
        Ok(bytes)
    }

    fn value_roundtrips_to<V: EncodeAsType, T: PartialEq + Debug + Decode + TypeInfo + 'static>(
        value: V,
        target: T,
    ) {
        let bytes = encode_type::<_, T>(&value).expect("can encode");
        let bytes_cursor = &mut &*bytes;
        let new_target = T::decode(bytes_cursor).expect("can decode");

        assert_eq!(bytes_cursor.len(), 0, "no bytes should be remaining");
        assert_eq!(
            target, new_target,
            "value does not roundtrip and decode to target"
        );
    }

    fn encodes_like_codec<V: Encode + EncodeAsType + PartialEq + Debug + TypeInfo + 'static>(
        value: V,
    ) {
        let encode_bytes = value.encode();
        let bytes = encode_type::<V, V>(value).expect("can encode");
        assert_eq!(
            bytes, encode_bytes,
            "scale-encode encoded differently from parity-scale-codec"
        );
    }

    #[test]
    fn numeric_roundtrips_encode_ok() {
        macro_rules! int_value_roundtrip {
            ($($val:expr; $ty:ty),+) => {$(
                value_roundtrips_to($val, $val as i8);
                value_roundtrips_to($val, $val as i16);
                value_roundtrips_to($val, $val as i32);
                value_roundtrips_to($val, $val as i64);
                value_roundtrips_to($val, $val as i128);
            )+}
        }
        macro_rules! uint_value_roundtrip {
            ($($val:expr; $ty:ty),+) => {$(
                value_roundtrips_to($val, $val as u8);
                value_roundtrips_to($val, $val as u16);
                value_roundtrips_to($val, $val as u32);
                value_roundtrips_to($val, $val as u64);
                value_roundtrips_to($val, $val as u128);
            )+}
        }
        macro_rules! int_value_roundtrip_types {
            ($($val:expr),+) => {$(
                int_value_roundtrip!($val; i8);
                int_value_roundtrip!($val; i16);
                int_value_roundtrip!($val; i32);
                int_value_roundtrip!($val; i64);
                int_value_roundtrip!($val; i128);
            )+}
        }
        macro_rules! uint_value_roundtrip_types {
            ($($val:expr),+) => {$(
                uint_value_roundtrip!($val; u8);
                uint_value_roundtrip!($val; u16);
                uint_value_roundtrip!($val; u32);
                uint_value_roundtrip!($val; u64);
                uint_value_roundtrip!($val; u128);
            )+}
        }
        macro_rules! all_value_roundtrip_types {
            ($($val:expr),+) => {$(
                int_value_roundtrip_types!($val);
                uint_value_roundtrip_types!($val);
            )+}
        }
        uint_value_roundtrip_types!(200);
        int_value_roundtrip_types!(-127, -100, 0, 1, 100, 127);
        all_value_roundtrip_types!(0, 1, 100, 127);
    }

    #[test]
    fn out_of_range_numeric_roundtrips_fail_to_encode() {
        encode_type::<_, u8>(&1234u16).unwrap_err();
        encode_type::<_, i8>(&129u8).unwrap_err();
        encode_type::<_, u8>(&-10i8).unwrap_err();
    }

    #[test]
    fn sequence_encodes_like_scale_codec() {
        let (type_id, types) = make_type::<Vec<u8>>();
        let e = vec![1u8, 2, 3].encode();
        let e2 = vec![1u8, 2, 3]
            .encode_as_type(type_id, &types)
            .expect("can encode 2");
        assert_eq!(e, e2);
    }

    #[test]
    fn basic_types_encode_like_scale_codec() {
        encodes_like_codec(true);
        encodes_like_codec(false);
        encodes_like_codec("hi");
        encodes_like_codec("hi".to_string());
        encodes_like_codec(Box::new("hi"));
        encodes_like_codec(-1234);
        encodes_like_codec(100_000_000_000_000u128);
        encodes_like_codec(());
        encodes_like_codec(std::marker::PhantomData::<()>);
        encodes_like_codec([1, 2, 3, 4, 5]);
        encodes_like_codec([1u8, 2, 3, 4, 5]);
        encodes_like_codec(vec![1, 2, 3, 4, 5]);
        encodes_like_codec([1, 2, 3, 4, 5]);
        encodes_like_codec(Some(1234u32));
        encodes_like_codec(None as Option<bool>);
        encodes_like_codec(Ok::<_, &str>("hello"));
        encodes_like_codec(Err::<u32, _>("aah"));
        encodes_like_codec(0..100);
        encodes_like_codec(0..=100);

        // These don't impl TypeInfo so we have to provide the target type to encode to & compare with:
        value_roundtrips_to(Arc::new("hi"), "hi".to_string());
        value_roundtrips_to(Rc::new("hi"), "hi".to_string());
        // encodes_like_codec(std::time::Duration::from_millis(123456));
    }

    #[test]
    fn other_container_types_roundtrip_ok() {
        // These things don't have TypeInfo impls, and so we just assume that they should
        // encode like any sequence, prefixed with length.

        let v = LinkedList::from([1u8, 2, 3]);
        value_roundtrips_to(v, vec![1u8, 2, 3]);

        // (it's a max heap, so values ordered max first.)
        let v = BinaryHeap::from([2, 3, 1]);
        value_roundtrips_to(v, vec![3u8, 2, 1]);

        let v = BTreeSet::from([1u8, 2, 3]);
        value_roundtrips_to(v, vec![1u8, 2, 3]);

        let v = VecDeque::from([1u8, 2, 3]);
        value_roundtrips_to(v, vec![1u8, 2, 3]);
    }

    #[test]
    fn btreemap_can_encode_to_struct() {
        #[derive(Debug, scale_info::TypeInfo, codec::Decode, PartialEq)]
        struct Foo {
            a: u8,
            b: (bool,),
            c: String,
        }

        let v = BTreeMap::from([
            ("a", &1u8 as &dyn EncodeAsType),
            ("c", &"hello" as &dyn EncodeAsType),
            ("b", &true as &dyn EncodeAsType),
        ]);

        // BTreeMap can go to a key-val composite, or unnamed:
        value_roundtrips_to(
            v.clone(),
            Foo {
                a: 1,
                b: (true,),
                c: "hello".to_string(),
            },
        );
        value_roundtrips_to(v, (1, true, "hello".to_string()));
    }

    #[test]
    fn mixed_tuples_roundtrip_ok() {
        encodes_like_codec(());
        encodes_like_codec((12345,));
        encodes_like_codec((123u8, true));
        encodes_like_codec((123u8, true, "hello"));
        // Encode isn't implemented for `char` (but we treat it as a u32):
        encodes_like_codec((123u8, true, "hello".to_string(), 'a' as u32));
        encodes_like_codec((
            123u8,
            true,
            "hello".to_string(),
            'a' as u32,
            123_000_000_000u128,
        ));
    }

    #[test]
    fn sequences_roundtrip_into_eachother() {
        // Tuples can turn to sequences or arrays:
        value_roundtrips_to((1u8, 2u8, 3u8), vec![1u8, 2u8, 3u8]);
        value_roundtrips_to((1u8, 2u8, 3u8), [1u8, 2u8, 3u8]);

        // Even when inner types differ but remain compatible on either side.
        value_roundtrips_to((1u8, 2u8, 3u8), vec![1u128, 2u128, 3u128]);
        value_roundtrips_to((1u8, 2u8, 3u8), vec![(1u128,), (2u128,), (3u128,)]);
        value_roundtrips_to(((1u8,), (2u8,), 3u8), vec![1u128, 2u128, 3u128]);
        value_roundtrips_to((([[1u8]],), (2u8,), 3u8), vec![1u128, 2u128, 3u128]);

        // tuples can also encode to structs of same lengths (with inner type compat):
        #[derive(Debug, scale_info::TypeInfo, codec::Decode, PartialEq)]
        struct Foo {
            a: (u32,),
            b: u64,
            c: u128,
        }
        value_roundtrips_to(
            (1u8, 2u8, 3u8),
            Foo {
                a: (1,),
                b: 2,
                c: 3,
            },
        );
    }

    #[test]
    fn values_roundtrip_into_wrappers() {
        #[derive(Debug, scale_info::TypeInfo, codec::Decode, PartialEq)]
        struct Wrapper<T> {
            val: T,
        }

        value_roundtrips_to(true, ([true],));
        value_roundtrips_to(1234u16, ([1234u16],));
        value_roundtrips_to(1234u16, Wrapper { val: 1234u16 });
        value_roundtrips_to("hi", (["hi".to_string()],));
        value_roundtrips_to(
            "hi",
            ([Wrapper {
                val: "hi".to_string(),
            }],),
        );

        // Sequence types will try to unwrap composite/tuple things in the target type to
        // find a sequenceish thing to encode to.
        value_roundtrips_to(vec![1i128], (Wrapper { val: vec![1i128] },));
        // and as a last5 ditch attempt we'll unwrap a single value in a sequence type and
        // try encoding to that.
        value_roundtrips_to(vec![1i128], (Wrapper { val: 1i128 },));
    }

    #[test]
    fn compacts_roundtrip() {
        encodes_like_codec(Compact(123u16));
        encodes_like_codec(Compact(123u8));
        encodes_like_codec(Compact(123u64));
    }

    #[test]
    fn tuple_composite_can_encode_to_named_structs() {
        #[derive(Debug, scale_info::TypeInfo, codec::Decode, PartialEq)]
        struct Foo {
            bar: u32,
            wibble: bool,
            hello: String,
        }

        // note: fields do not need to be in order when named:
        let vals = [
            (Some("hello"), &("world".to_string()) as &dyn EncodeAsType),
            (Some("bar"), &12345u128 as &dyn EncodeAsType),
            (Some("wibble"), &true as &dyn EncodeAsType),
        ];
        let source = Composite(vals.iter().copied());

        let target = Foo {
            bar: 12345,
            wibble: true,
            hello: "world".to_string(),
        };

        value_roundtrips_to(source, target);
    }

    #[test]
    fn tuple_composite_can_encode_to_unnamed_structs() {
        #[derive(Debug, scale_info::TypeInfo, codec::Decode, PartialEq, Clone)]
        struct Foo(u32, bool, String);

        // note: unnamed target so fields need to be in order (can be named or not)
        let named_vals = [
            (Some("bar"), &12345u128 as &dyn EncodeAsType),
            (Some("wibble"), &true as &dyn EncodeAsType),
            (Some("hello"), &"world".to_string() as &dyn EncodeAsType),
        ];
        let source = Composite(named_vals.iter().copied());

        let unnamed_vals = [
            (None, &12345u128 as &dyn EncodeAsType),
            (None, &true as &dyn EncodeAsType),
            (None, &"world".to_string() as &dyn EncodeAsType),
        ];
        let source2 = Composite(unnamed_vals.iter().copied());

        let target = Foo(12345, true, "world".to_string());

        value_roundtrips_to(source, target.clone());
        value_roundtrips_to(source2, target);
    }

    #[test]
    fn tuple_composite_names_must_line_up() {
        #[derive(Debug, scale_info::TypeInfo, codec::Decode, PartialEq)]
        struct Foo {
            bar: u32,
            wibble: bool,
            hello: String,
        }

        // note: fields do not need to be in order when named:
        let vals = [
            (Some("hello"), &"world".to_string() as &dyn EncodeAsType),
            (Some("bar"), &12345u128 as &dyn EncodeAsType),
            // wrong name:
            (Some("wibbles"), &true as &dyn EncodeAsType),
        ];
        let source = Composite(vals.iter().copied());

        encode_type::<_, Foo>(source).unwrap_err();
    }

    #[cfg(feature = "bits")]
    #[test]
    fn bits_roundtrip_ok() {
        use bitvec::{
            order::{Lsb0, Msb0},
            vec::BitVec,
        };
        use scale_bits::Bits;

        fn test_bits(bits: impl IntoIterator<Item = bool> + Clone) {
            let source = Bits::from_iter(bits.clone());

            let target = BitVec::<u8, Lsb0>::from_iter(bits.clone());
            value_roundtrips_to(source.clone(), target);
            let target = BitVec::<u16, Lsb0>::from_iter(bits.clone());
            value_roundtrips_to(source.clone(), target);
            let target = BitVec::<u32, Lsb0>::from_iter(bits.clone());
            value_roundtrips_to(source.clone(), target);
            let target = BitVec::<u64, Lsb0>::from_iter(bits.clone());
            value_roundtrips_to(source.clone(), target);
            let target = BitVec::<u8, Msb0>::from_iter(bits.clone());
            value_roundtrips_to(source.clone(), target);
            let target = BitVec::<u16, Msb0>::from_iter(bits.clone());
            value_roundtrips_to(source.clone(), target);
            let target = BitVec::<u32, Msb0>::from_iter(bits.clone());
            value_roundtrips_to(source.clone(), target);
            let target = BitVec::<u64, Msb0>::from_iter(bits);
            value_roundtrips_to(source, target);
        }

        test_bits([]);
        test_bits([true]);
        test_bits([false]);
        test_bits([true, false, true, true, false]);
        test_bits([
            true, false, true, true, false, true, false, true, true, false, false,
        ]);

        // Wrapping the input or output bitvecs is fine; it'll figure it out:
        value_roundtrips_to(
            Bits::from_iter([true, false, true]),
            ((BitVec::<u8, Lsb0>::from_iter([true, false, true]),),),
        );
        value_roundtrips_to(
            (Bits::from_iter([true, false, true]),),
            ((BitVec::<u8, Lsb0>::from_iter([true, false, true]),),),
        );
    }

    #[cfg(feature = "primitive-types")]
    #[test]
    fn hxxx_types_roundtrip_ok() {
        use ::primitive_types::{H128, H160, H256, H384, H512, H768};

        // Check that Hxxx types roundtirp to themselves or to byte sequences
        fn test_hxxx(bytes: impl IntoIterator<Item = u8> + Clone) {
            let mut bytes: Vec<u8> = bytes.into_iter().collect();

            while bytes.len() < 128 / 8 {
                bytes.push(0)
            }
            value_roundtrips_to(H128::from_slice(&bytes), bytes.clone());
            value_roundtrips_to(H128::from_slice(&bytes), H128::from_slice(&bytes));

            while bytes.len() < 160 / 8 {
                bytes.push(0)
            }
            value_roundtrips_to(H160::from_slice(&bytes), bytes.clone());
            value_roundtrips_to(H160::from_slice(&bytes), H160::from_slice(&bytes));

            while bytes.len() < 256 / 8 {
                bytes.push(0)
            }
            value_roundtrips_to(H256::from_slice(&bytes), bytes.clone());
            value_roundtrips_to(H256::from_slice(&bytes), H256::from_slice(&bytes));

            while bytes.len() < 384 / 8 {
                bytes.push(0)
            }
            value_roundtrips_to(H384::from_slice(&bytes), bytes.clone());
            value_roundtrips_to(H384::from_slice(&bytes), H384::from_slice(&bytes));

            while bytes.len() < 512 / 8 {
                bytes.push(0)
            }
            value_roundtrips_to(H512::from_slice(&bytes), bytes.clone());
            value_roundtrips_to(H512::from_slice(&bytes), H512::from_slice(&bytes));

            while bytes.len() < 768 / 8 {
                bytes.push(0)
            }
            value_roundtrips_to(H768::from_slice(&bytes), bytes.clone());
            value_roundtrips_to(H768::from_slice(&bytes), H768::from_slice(&bytes));
        }

        test_hxxx([0u8]);
        test_hxxx([1, 2, 3, 4]);
    }
}
