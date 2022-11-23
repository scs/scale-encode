use scale_info::{
    PortableRegistry,
    TypeDef,
    TypeDefPrimitive,
};
use codec::{
    Encode,
    Compact
};
use crate::{ EncodeAsType, Error, Context, Kind, ErrorKind, NumericKind };
use core::num::{
    NonZeroU8,
    NonZeroU16,
    NonZeroU32,
    NonZeroU64,
    NonZeroU128,
    NonZeroI8,
    NonZeroI16,
    NonZeroI32,
    NonZeroI64,
    NonZeroI128,
};
use std::sync::Arc;
use std::rc::Rc;
use std::marker::PhantomData;
use core::ops::{ Range, RangeInclusive };
use std::time::Duration;
use std::collections::{
    BTreeMap, BTreeSet, BinaryHeap, VecDeque, LinkedList
};

impl EncodeAsType for bool {
    fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
        let type_id = find_single_entry_with_same_repr(type_id, types).unwrap_or(type_id);
        let ty = types
            .resolve(type_id)
            .ok_or_else(|| Error::new(&context, ErrorKind::TypeNotFound(type_id)))?;

        if let TypeDef::Primitive(TypeDefPrimitive::Bool) = ty.type_def() {
            self.encode_to(out);
            Ok(())
        } else {
            Err(Error::new(context, ErrorKind::WrongShape { actual: Kind::Bool, expected: type_id }))
        }
    }
}

impl EncodeAsType for str {
    fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
        let type_id = find_single_entry_with_same_repr(type_id, types).unwrap_or(type_id);
        let ty = types
            .resolve(type_id)
            .ok_or_else(|| Error::new(&context, ErrorKind::TypeNotFound(type_id)))?;

        if let TypeDef::Primitive(TypeDefPrimitive::Str) = ty.type_def() {
            self.encode_to(out);
            Ok(())
        } else {
            Err(Error::new(context, ErrorKind::WrongShape { actual: Kind::Str, expected: type_id }))
        }
    }
}

impl <'a, T> EncodeAsType for &'a T where T: EncodeAsType {
    fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
        (*self).encode_as_type_to(type_id, types, context, out)
    }
}

impl <'a, T> EncodeAsType for std::borrow::Cow<'a, T> where T: EncodeAsType + Clone {
    fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
        (**self).encode_as_type_to(type_id, types, context, out)
    }
}

impl <T> EncodeAsType for [T] where T: EncodeAsType {
    fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
        encode_iterable_sequence_to(self.len(), self.iter(), type_id, types, context, out)
    }
}

impl <const N: usize, T: EncodeAsType> EncodeAsType for [T; N] {
    fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
		self[..].encode_as_type_to(type_id, types, context, out)
    }
}

// Encode any numeric type implementing ToNumber, above, into the type ID given.
macro_rules! impl_encode_number {
    ($ty:ty) => {
        impl EncodeAsType for $ty {
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
                let type_id = find_single_entry_with_same_repr(type_id, types).unwrap_or(type_id);

                let ty = types
                    .resolve(type_id)
                    .ok_or_else(|| Error::new(&context, ErrorKind::TypeNotFound(type_id)))?;

                fn try_num<T: TryFrom<$ty> + Encode>(num: $ty, context: Context, target_kind: NumericKind, out: &mut Vec<u8>) -> Result<(), Error> {
                    let n: T = num.try_into().map_err(|_| Error::new(context, ErrorKind::NumberOutOfRange { value: num.to_string(), target_type: target_kind }))?;
                    n.encode_to(out);
                    Ok(())
                }

                match ty.type_def() {
                    TypeDef::Primitive(TypeDefPrimitive::U8) => {
                        try_num::<u8>(*self, context, NumericKind::U8, out)
                    },
                    TypeDef::Primitive(TypeDefPrimitive::U16) => {
                        try_num::<u16>(*self, context, NumericKind::U16, out)
                    },
                    TypeDef::Primitive(TypeDefPrimitive::U32) => {
                        try_num::<u32>(*self, context, NumericKind::U32, out)
                    },
                    TypeDef::Primitive(TypeDefPrimitive::U64) => {
                        try_num::<u64>(*self, context, NumericKind::U64, out)
                    },
                    TypeDef::Primitive(TypeDefPrimitive::U128) => {
                        try_num::<u128>(*self, context, NumericKind::U128, out)
                    },
                    TypeDef::Primitive(TypeDefPrimitive::I8) => {
                        try_num::<i8>(*self, context, NumericKind::I8, out)
                    },
                    TypeDef::Primitive(TypeDefPrimitive::I16) => {
                        try_num::<i16>(*self, context, NumericKind::I16, out)
                    },
                    TypeDef::Primitive(TypeDefPrimitive::I32) => {
                        try_num::<i32>(*self, context, NumericKind::I32, out)
                    },
                    TypeDef::Primitive(TypeDefPrimitive::I64) => {
                        try_num::<i64>(*self, context, NumericKind::I64, out)
                    },
                    TypeDef::Primitive(TypeDefPrimitive::I128) => {
                        try_num::<i128>(*self, context, NumericKind::I128, out)
                    },
                    TypeDef::Compact(c) => {
                        let type_id = find_single_entry_with_same_repr(c.type_param().id(), types).ok_or_else(|| Error::new(&context, ErrorKind::CannotEncodeToType {
                            id: type_id,
                            reason: "compact encoded types must be numbers, or single-field tuples, arrays or composites ultimately containing numbers"
                        }))?;

                        let ty = types
                            .resolve(type_id)
                            .ok_or_else(|| Error::new(&context, ErrorKind::TypeNotFound(type_id)))?;

                        macro_rules! try_compact_num {
                            ($num:expr, $context:expr, $target_kind:expr, $out:expr, $type:ty) => {{
                                let n: $type = $num.try_into().map_err(|_| Error::new($context, ErrorKind::NumberOutOfRange { value: $num.to_string(), target_type: $target_kind }))?;
                                Compact(n).encode_to($out);
                                Ok(())
                            }}
                        }

                        match ty.type_def() {
                            TypeDef::Primitive(TypeDefPrimitive::U8) => {
                                try_compact_num!(*self, context, NumericKind::U8, out, u8)
                            },
                            TypeDef::Primitive(TypeDefPrimitive::U16) => {
                                try_compact_num!(*self, context, NumericKind::U16, out, u16)
                            },
                            TypeDef::Primitive(TypeDefPrimitive::U32) => {
                                try_compact_num!(*self, context, NumericKind::U32, out, u32)
                            },
                            TypeDef::Primitive(TypeDefPrimitive::U64) => {
                                try_compact_num!(*self, context, NumericKind::U64, out, u64)
                            },
                            TypeDef::Primitive(TypeDefPrimitive::U128) => {
                                try_compact_num!(*self, context, NumericKind::U128, out, u128)
                            },
                            _ => {
                                Err(Error::new(context, ErrorKind::WrongShape {
                                    actual: Kind::Number,
                                    expected: type_id
                                }))
                            }
                        }
                    },
                    _ => {
                        Err(Error::new(context, ErrorKind::WrongShape {
                            actual: Kind::Number,
                            expected: type_id
                        }))
                    }
                }
            }
        }
    }
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

// Count the number of types provided.
macro_rules! count_idents {
    () => (0usize);
    ( $t:ident, $($ts:ident,)* ) => (1usize + count_idents!($($ts,)*));
}

// Encode tuple types to any matching type.
macro_rules! impl_encode_tuple {
    ($($name:ident: $t:ident),*) => {
        impl < $($t),* > EncodeAsType for ($($t,)*) where $($t: EncodeAsType),* {
            #[allow(unused_assignments)]
            #[allow(unused_mut)]
            #[allow(unused_variables)]
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
                let ($($name,)*) = self;

                let len = count_idents!($($t,)*);
                let ty = types
                    .resolve(type_id)
                    .ok_or_else(|| Error::new(&context, ErrorKind::TypeNotFound(type_id)))?;

                // As long as the lengths line up, to the number of tuple items, we'll
                // do our best to encode each inner type as needed.
                match ty.type_def() {
                    TypeDef::Tuple(tuple) if tuple.fields().len() == len => {
                        let fields = tuple.fields();
                        let mut idx = 0;
                        $({
                            let mut context = context.clone();
                            context.push_idx(idx);
                            $name.encode_as_type_to(fields[idx].id(), types, context, out)?;
                            idx += 1;
                        })*
                        Ok(())
                    },
                    TypeDef::Composite(composite) if composite.fields().len() == len => {
                        let fields = composite.fields();
                        let mut idx = 0;
                        $({
                            let mut context = context.clone();
                            context.push_idx(idx);
                            $name.encode_as_type_to(fields[idx].ty().id(), types, context, out)?;
                            idx += 1;
                        })*
                        Ok(())
                    },
                    TypeDef::Array(array) if array.len() == len as u32 => {
                        let mut idx = 0;
                        $({
                            let mut context = context.clone();
                            context.push_idx(idx);
                            $name.encode_as_type_to(array.type_param().id(), types, context, out)?;
                            idx += 1;
                        })*
                        Ok(())
                    },
                    _ => {
                        Err(Error::new(context, ErrorKind::WrongShape { actual: Kind::Tuple, expected: type_id }))
                    }
                }
            }
        }
    }
}
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

// Encode our basic Option and Result enum types.
macro_rules! impl_encode_basic_enum {
    ($name:ident<$($ty:ident),*>: $($variant:ident $( ($val:ident) )?),+) => {
        impl <$($ty),*> EncodeAsType for $name<$($ty),*> where $($ty: EncodeAsType),* {
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
                let type_id = find_single_entry_with_same_repr(type_id, types).unwrap_or(type_id);
                let ty = types
                    .resolve(type_id)
                    .ok_or_else(|| Error::new(&context, ErrorKind::TypeNotFound(type_id)))?;

                match ty.type_def() {
                    TypeDef::Variant(var) => {
                        let vars = var.variants();
                        match self {
                            $(
                                $variant $( ($val) )? => {
                                    let Some(v) = vars.iter().find(|v| v.name == stringify!($variant)) else {
                                        return Err(Error::new(context, ErrorKind::CannotFindVariant { name: stringify!($variant).into(), expected: type_id }));
                                    };
                                    if v.fields().len() != count_idents!($($val,)*) {
                                        return Err(Error::new(context, ErrorKind::WrongLength { actual_len: v.fields().len(), expected_len: 1, expected: type_id }));
                                    }
                                    v.index().encode_to(out);
                                    $( $val.encode_as_type_to(v.fields()[0].ty().id(), types, context, out)?; )?
                                    Ok(())
                                }
                            )*
                        }
                    },
                    _ => {
                        Err(Error::new(context, ErrorKind::WrongShape { actual: Kind::Str, expected: type_id }))
                    }
                }
            }
        }
    }
}
impl_encode_basic_enum!(Option<T>: Some(val), None);
impl_encode_basic_enum!(Result<T, E>: Ok(val), Err(e));

// Implement encoding via iterators for ordered collections
macro_rules! impl_encode_seq_via_iterator {
    ($ty:ident $( [$($param:ident),+] )?) => {
        impl $(< $($param),+ >)? EncodeAsType for $ty $(< $($param),+ >)?
        where $( $($param: EncodeAsType),+ )?
        {
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
                encode_iterable_sequence_to(self.len(), self.iter(), type_id, types, context, out)
            }
        }
    }
}
impl_encode_seq_via_iterator!(BTreeMap[K, V]);
impl_encode_seq_via_iterator!(BTreeSet[K]);
impl_encode_seq_via_iterator!(LinkedList[V]);
impl_encode_seq_via_iterator!(BinaryHeap[V]);
impl_encode_seq_via_iterator!(VecDeque[V]);
impl_encode_seq_via_iterator!(Vec[V]);

// Generate EncodeAsType impls for simple types that can be easily transformed
// into types we have impls for already.
macro_rules! impl_encode_like {
    ($ty:ident $(<$( $param:ident ),+>)? as $delegate_ty:ty where |$val:ident| $expr:expr) => {
        impl $(< $($param: EncodeAsType),+ >)? EncodeAsType for $ty $(<$( $param ),+>)? {
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
                let delegate: $delegate_ty = {
                    let $val = self;
                    $expr
                };
                delegate.encode_as_type_to(type_id, types, context, out)
            }
        }
    }
}
impl_encode_like!(String as &str where |val| &*val);
impl_encode_like!(Box<T> as &T where |val| &*val);
impl_encode_like!(Arc<T> as &T where |val| &*val);
impl_encode_like!(Rc<T> as &T where |val| &*val);
impl_encode_like!(PhantomData<T> as () where |_val| ());
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
impl_encode_like!(RangeInclusive<T> as (&T, &T) where |val| (&val.start(), &val.end()));

// Recurse into a type, looking for a single entry or returning None if there are
// multiple entries or otherwise this is not possible. If the thing you're trying to encode
// is some primitive type, you should probably use this to increase the chance of being able to encode.
fn find_single_entry_with_same_repr(type_id: u32, types: &PortableRegistry) -> Option<u32> {
    let ty = types.resolve(type_id)?;
    match ty.type_def() {
        TypeDef::Tuple(tuple) => {
            if tuple.fields().len() == 1 {
                find_single_entry_with_same_repr(tuple.fields()[0].id(), types)
            } else {
                None
            }
        },
        TypeDef::Composite(composite) => {
            if composite.fields().len() == 1 {
                find_single_entry_with_same_repr(composite.fields()[0].ty().id(), types)
            } else {
                None
            }
        },
        TypeDef::Array(arr) => {
            if arr.len() == 1 {
                find_single_entry_with_same_repr(arr.type_param().id(), types)
            } else {
                None
            }
        }
        _ => Some(type_id)
    }
}

// Encode some iterator of items to the type provided.
fn encode_iterable_sequence_to<I>(len: usize, it: I, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error>
where
    I: Iterator,
    I::Item: EncodeAsType
{
    let ty = types
        .resolve(type_id)
        .ok_or_else(|| Error::new(&context, ErrorKind::TypeNotFound(type_id)))?;

    match ty.type_def() {
        TypeDef::Array(arr) => {
            if arr.len() == len as u32 {
                for (idx, item) in it.enumerate() {
                    let mut context = context.clone();
                    context.push_idx(idx);
                    item.encode_as_type_to(arr.type_param().id(), types, context, out)?;
                }
                Ok(())
            } else {
                Err(Error::new(context, ErrorKind::WrongLength {
                    actual_len: len,
                    expected_len: arr.len() as usize,
                    expected: type_id
                }))
            }
        },
        TypeDef::Sequence(seq) => {
            for (idx, item) in it.enumerate() {
                let mut context = context.clone();
                context.push_idx(idx);
                // Sequences are prefixed with their compact encoded length:
                Compact(len as u32).encode_to(out);
                item.encode_as_type_to(seq.type_param().id(), types, context, out)?;
            }
            Ok(())
        },
        _ => {
            Err(Error::new(context, ErrorKind::WrongShape { actual: Kind::Array, expected: type_id }))
        }
    }
}