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

use crate::{
    error::{Error, ErrorKind, Kind, Location},
    EncodeAsType,
};
use codec::{Compact, Encode};
use scale_info::{form::PortableForm, Field, PortableRegistry, TypeDef};
use std::collections::HashMap;

/// This type represents named or unnamed composite values, and can be used
/// to help generate `EncodeAsType` impls. It's primarily used by the exported
/// macros to do just that.
///
/// ```rust
/// use scale_encode::utils::{ Composite, PortableRegistry };
/// use scale_encode::{ Error, EncodeAsType };
///
/// struct MyType {
///    foo: bool,
///    bar: u64,
///    wibble: String
/// }
///
/// impl EncodeAsType for MyType {
///     fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, out: &mut Vec<u8>) -> Result<(), Error> {
///         Composite((
///             (Some("foo"), &self.foo),
///             (Some("bar"), &self.bar),
///             (Some("wibble"), &self.wibble)
///         )).encode_as_type_to(type_id, types, out)
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
    ($($name:ident: $t:ident ,)*) => {
        impl < $($t),* > EncodeAsType for Composite<( $((Option<&'static str>, $t),)* )> where $($t: EncodeAsType),* {
            #[allow(unused_assignments)]
            #[allow(unused_mut)]
            #[allow(unused_variables)]
            fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, out: &mut Vec<u8>) -> Result<(), Error> {
                let ($($name,)*) = &self.0;

                const LEN: usize = count_idents!($($t,)*);
                let ty = types
                    .resolve(type_id)
                    .ok_or_else(|| Error::new(ErrorKind::TypeNotFound(type_id)))?;

                // As long as the lengths line up, to the number of tuple items, we'll
                // do our best to encode each inner type as needed.
                match ty.type_def() {
                    TypeDef::Tuple(tuple) if tuple.fields().len() == LEN => {
                        let fields = tuple.fields();
                        let mut idx = 0;
                        $({
                            let loc = if let Some(name) = $name.0 {
                                Location::field(name)
                            } else {
                                Location::idx(idx)
                            };
                            $name.1
                                .encode_as_type_to(fields[idx].id(), types, out)
                                .map_err(|e| e.at(loc))?;
                            idx += 1;
                        })*
                        Ok(())
                    },
                    TypeDef::Array(array) if array.len() == LEN as u32 => {
                        let mut idx = 0;
                        $({
                            let loc = if let Some(name) = $name.0 {
                                Location::field(name)
                            } else {
                                Location::idx(idx)
                            };
                            $name.1
                                .encode_as_type_to(array.type_param().id(), types, out)
                                .map_err(|e| e.at(loc))?;
                            idx += 1;
                        })*
                        Ok(())
                    },
                    TypeDef::Sequence(seq) => {
                        let mut idx = 0;
                        // sequences start with compact encoded length:
                        Compact(LEN as u32).encode_to(out);
                        $({
                            let loc = if let Some(name) = $name.0 {
                                Location::field(name)
                            } else {
                                Location::idx(idx)
                            };
                            $name.1
                                .encode_as_type_to(seq.type_param().id(), types, out)
                                .map_err(|e| e.at(loc))?;
                            idx += 1;
                        })*
                        Ok(())
                    },
                    TypeDef::Composite(composite) if composite.fields().len() == LEN => {
                        let fields = composite.fields();
                        self.encode_fields_to(fields, type_id, types, out)
                    },
                    _ => {
                        // Tuple with 1 entry? before giving up, try encoding the inner entry instead:
                        if LEN == 1 {
                            // We only care about the case where there is exactly one copy of
                            // this, but have to accomodate the cases where multiple copies and assume
                            // that the compielr can easily optimise out this branch for LEN != 1.
                            $({
                                $name.1
                                    .encode_as_type_to(type_id, types, out)
                                    .map_err(|e| e.at_idx(0))?;
                            })*
                            Ok(())
                        } else {
                            Err(Error::new(ErrorKind::WrongShape { actual: Kind::Tuple, expected: type_id }))
                        }
                    }
                }
            }
        }
    }
}

/// A helper trait to encode composite fields. This exists so that we can reuse the same logic for variant fields, too.
/// It doesn't actually need publically exposing.
pub(crate) trait EncodeFieldsAsType {
    fn encode_fields_to(
        &self,
        fields: &[Field<PortableForm>],
        type_id: u32,
        types: &PortableRegistry,
        out: &mut Vec<u8>,
    ) -> Result<(), Error>;
}

macro_rules! impl_encode_composite_fields {
    ($($name:ident: $t:ident ,)*) => {
        impl < $($t),* > EncodeFieldsAsType for Composite<( $((Option<&'static str>, $t),)* )> where $($t: EncodeAsType),* {
            #[allow(unused_assignments)]
            #[allow(unused_mut)]
            #[allow(unused_variables)]
            fn encode_fields_to(&self, fields: &[Field<PortableForm>], type_id: u32, types: &PortableRegistry, out: &mut Vec<u8>) -> Result<(), Error> {
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
                            return Err(Error::new(ErrorKind::CannotFindField { name: name.to_string() }))
                        };

                        // Encode the value to the output:
                        value.encode_as_type_to(field.ty().id(), types, out)
                            .map_err(|e| e.at_field(name.to_string()))?;
                    }

                    Ok(())
                } else {
                    // target fields aren't named, so encode by order only. We need the field length
                    // to line up for this to work.
                    if fields.len() != LEN {
                        return Err(Error::new(ErrorKind::WrongLength {
                            actual_len: LEN,
                            expected_len: fields.len(),
                            expected: type_id
                        }))
                    }

                    let mut idx = 0;
                    $({
                        let loc = if let Some(name) = $name.0 {
                            Location::field(name)
                        } else {
                            Location::idx(idx)
                        };
                        $name.1
                            .encode_as_type_to(fields[idx].ty().id(), types, out)
                            .map_err(|e| e.at(loc))?;
                        idx += 1;
                    })*
                    Ok(())
                }
            }
        }
    }
}

// Generate encodings for a load of fields (I've seen 40+ in types seen in metadata before).
macro_rules! impl_encodes {
    ($name:ident: $t:ident, $($rest:tt)*) => {
        impl_encode_composite!($name: $t, $($rest)*);
        impl_encode_composite_fields!($name: $t, $($rest)*);
        impl_encodes!($($rest)*);
    };
    () => {
        impl_encode_composite!();
        impl_encode_composite_fields!();
    }
}
#[rustfmt::skip]
impl_encodes!(
  a0: A0, b0: B0, c0: C0, d0: D0, e0: E0, f0: F0, g0: G0, h0: H0, i0: I0, j0: J0, k0: K0, l0: L0, m0: M0, n0: N0, o0: O0, p0: P0, q0: Q0, r0: R0, s0: S0, t0: T0, u0: U0, v0: V0, w0: W0, x0: X0, y0: Y0, z0: Z0,
  a1: A1, b1: B1, c1: C1, d1: D1, e1: E1, f1: F1, g1: G1, h1: H1, i1: I1, j1: J1, k1: K1, l1: L1, m1: M1, n1: N1, o1: O1, p1: P1, q1: Q1, r1: R1, s1: S1, t1: T1, u1: U1, v1: V1, w1: W1, x1: X1, y1: Y1, z1: Z1,
  a2: A2, b2: B2, c2: C2, d2: D2, e2: E2, f2: F2, g2: G2, h2: H2, i2: I2, j2: J2, k2: K2, l2: L2, m2: M2, n2: N2, o2: O2, p2: P2, q2: Q2, r2: R2, s2: S2, t2: T2, u2: U2, v2: V2, w2: W2, x2: X2, y2: Y2, z2: Z2,
);
// ^ note: our derive macro delegates to this, so this is also the limit for hor many struct/variant fields will satisfy EncodeAsType before things break..
