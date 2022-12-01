use scale_info::{
    PortableRegistry,
    TypeDef,
    Field,
    form::PortableForm,
};
use codec::{
    Compact,
    Encode
};
use crate::{
    EncodeAsType,
    context::{ Context, Location },
    error::{ Error, ErrorKind, Kind }
};
use std::collections::HashMap;

/// This type represents named or unnamed composite values, and can be used
/// to help generate `EncodeAsType` impls. It's primarily used by the exported
/// macros to do just that.
///
/// ```rust
/// use scale_encode::utils::{ Composite, PortableRegistry };
/// use scale_encode::{ Error, Context, EncodeAsType };
///
/// struct MyType {
///    foo: bool,
///    bar: u64,
///    wibble: String
/// }
///
/// impl EncodeAsType for MyType {
///     fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
///         Composite((
///             (Some("foo"), &self.foo),
///             (Some("bar"), &self.bar),
///             (Some("wibble"), &self.wibble)
///         )).encode_as_type_to(type_id, types, context, out)
///     }
/// }
/// ```
#[doc(hidden)]
pub struct Composite<Tuples>(pub Tuples);

macro_rules! count_idents {
    () => (0usize);
    ( $t:ident, $($ts:ident,)* ) => (1usize + count_idents!($($ts,)*));
}

// `Composite(((Option<&'static str>, T),..))` where `T: EncodeAsType` will get an impl of `EncodeAsType` via this macro:
macro_rules! impl_encode_composite {
    ($($name:ident: $t:ident),*) => {
        impl < $($t),* > EncodeAsType for Composite<( $((Option<&'static str>, $t),)* )> where $($t: EncodeAsType),* {
            #[allow(unused_assignments)]
            #[allow(unused_mut)]
            #[allow(unused_variables)]
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
                let ($($name,)*) = &self.0;

                const LEN: usize = count_idents!($($t,)*);
                let ty = types
                    .resolve(type_id)
                    .ok_or_else(|| Error::new(context.clone(), ErrorKind::TypeNotFound(type_id)))?;

                // As long as the lengths line up, to the number of tuple items, we'll
                // do our best to encode each inner type as needed.
                match ty.type_def() {
                    TypeDef::Tuple(tuple) if tuple.fields().len() == LEN => {
                        let fields = tuple.fields();
                        let mut idx = 0;
                        $({
                            let context = if let Some(name) = $name.0 {
                                context.at(Location::field(name))
                            } else {
                                context.at(Location::idx(idx))
                            };
                            $name.1.encode_as_type_to(fields[idx].id(), types, context, out)?;
                            idx += 1;
                        })*
                        Ok(())
                    },
                    TypeDef::Array(array) if array.len() == LEN as u32 => {
                        let mut idx = 0;
                        $({
                            let context = if let Some(name) = $name.0 {
                                context.at(Location::field(name))
                            } else {
                                context.at(Location::idx(idx))
                            };
                            $name.1.encode_as_type_to(array.type_param().id(), types, context, out)?;
                            idx += 1;
                        })*
                        Ok(())
                    },
                    TypeDef::Sequence(seq) => {
                        let mut idx = 0;
                        // sequences start with compact encoded length:
                        Compact(LEN as u32).encode_to(out);
                        $({
                            let context = if let Some(name) = $name.0 {
                                context.at(Location::field(name))
                            } else {
                                context.at(Location::idx(idx))
                            };
                            $name.1.encode_as_type_to(seq.type_param().id(), types, context, out)?;
                            idx += 1;
                        })*
                        Ok(())
                    },
                    TypeDef::Composite(composite) if composite.fields().len() == LEN => {
                        let fields = composite.fields();
                        self.encode_fields_to(fields, type_id, types, context, out)
                    },
                    _ => {
                        // Tuple with 1 entry? before giving up, try encoding the inner entry instead:
                        if LEN == 1 {
                            // We only care about the case where there is exactly one copy of
                            // this, but have to accomodate the cases where multiple copies and assume
                            // that the compielr can easily optimise out this branch for LEN != 1.
                            $({
                                let context = context.at(Location::idx(0));
                                $name.1.encode_as_type_to(type_id, types, context, out)?;
                            })*
                            Ok(())
                        } else {
                            Err(Error::new(context, ErrorKind::WrongShape { actual: Kind::Tuple, expected: type_id }))
                        }
                    }
                }
            }
        }
    }
}
impl_encode_composite!();
impl_encode_composite!(a: A);
impl_encode_composite!(a: A, b: B);
impl_encode_composite!(a: A, b: B, c: C);
impl_encode_composite!(a: A, b: B, c: C, d: D);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1, c1: C1);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1, c1: C1, d1: D1);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1, c1: C1, d1: D1, e1: E1);
impl_encode_composite!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1, c1: C1, d1: D1, e1: E1, f1: F1);
// ^ note: our derive macro delegates to this, so this is also the limit for hor many struct/variant fields will satisfy EncodeAsType before things break..

/// A helper trait to encode composite fields. This exists so that we can reuse the same logic for variant fields, too.
/// It doesn't actually need publically exposing.
pub (crate) trait EncodeFieldsAsType {
    fn encode_fields_to(&self, fields: &[Field<PortableForm>], type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error>;
}

macro_rules! impl_encode_composite_fields {
    ($($name:ident: $t:ident),*) => {
        impl < $($t),* > EncodeFieldsAsType for Composite<( $((Option<&'static str>, $t),)* )> where $($t: EncodeAsType),* {
            #[allow(unused_assignments)]
            #[allow(unused_mut)]
            #[allow(unused_variables)]
            fn encode_fields_to(&self, fields: &[Field<PortableForm>], type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
                let ($($name,)*) = &self.0;
                const LEN: usize = count_idents!($($t,)*);

                // Both the target and source type have to have named fields for us to use
                // names to line them up.
                let is_named = {
                    let is_target_named = fields.iter().any(|f| f.name().is_some());

                    let mut is_source_named = false;
                    $(
                        if $name.0.is_some() { is_source_named = true }
                    )*
                    is_target_named && is_source_named
                };

                if is_named {
                    // target + source fields are named, so hash source values by name and
                    // then encode to the target type by matching the names. If fields are
                    // named, we don't even mind if the number of fields doesn't line up;
                    // we just ignore any fields we provided that aren't needed.
                    let source_fields_by_name = {
                        let mut s = HashMap::<&'static str, &dyn EncodeAsType>::new();
                        $(
                            s.insert($name.0.unwrap_or(""), &$name.1 as &dyn EncodeAsType);
                        )*
                        s
                    };

                    for field in fields {
                        // Find the field in our source type:
                        let name = field.name().map(|n| &**n).unwrap_or("");
                        let Some(value) = source_fields_by_name.get(name) else {
                            return Err(Error::new(context, ErrorKind::CannotFindField { name: name.to_string() }))
                        };

                        // Encode the value to the output:
                        let context = context.at(Location::field(name.to_string()));
                        value.encode_as_type_to(field.ty().id(), types, context, out)?;
                    }

                    Ok(())
                } else {
                    // target fields aren't named, so encode by order only. We need the field length
                    // to line up for this to work.
                    if fields.len() != LEN {
                        return Err(Error::new(context, ErrorKind::WrongLength {
                            actual_len: LEN,
                            expected_len: fields.len(),
                            expected: type_id
                        }))
                    }

                    let mut idx = 0;
                    $({
                        let context = if let Some(name) = $name.0 {
                            context.at(Location::field(name))
                        } else {
                            context.at(Location::idx(idx))
                        };
                        $name.1.encode_as_type_to(fields[idx].ty().id(), types, context, out)?;
                        idx += 1;
                    })*
                    Ok(())
                }
            }
        }
    }
}

impl_encode_composite_fields!();
impl_encode_composite_fields!(a: A);
impl_encode_composite_fields!(a: A, b: B);
impl_encode_composite_fields!(a: A, b: B, c: C);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1, c1: C1);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1, c1: C1, d1: D1);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1, c1: C1, d1: D1, e1: E1);
impl_encode_composite_fields!(a: A, b: B, c: C, d: D, e: E, f: F, g: G, h: H, i: I, j: J, k: K, l: L, m: M, n: N, o: O, p: P, q: Q, r: R, s: S, t: T, u: U, v: V, w: W, x: X, y: Y, z: Z, a1: A1, b1: B1, c1: C1, d1: D1, e1: E1, f1: F1);