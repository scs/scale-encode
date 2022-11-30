use scale_info::{
    PortableRegistry,
    TypeDef,
};
use codec::{
    Encode
};
use crate::{
    EncodeAsType,
    context::{ Context },
    error::{ Error, ErrorKind, Kind }
};
use super::composite::EncodeFieldsAsType;

/// This type represents some statically declared variant type. Derive macros
/// on enums will use this internall to benefit from the same logic and keep
/// them lightweight.
#[doc(hidden)]
pub struct Variant<Tuples> {
    pub name: &'static str,
    pub fields: super::composite::Composite<Tuples>
}

impl <Tuples> EncodeAsType for Variant<Tuples> where super::composite::Composite<Tuples>: EncodeFieldsAsType {
    fn encode_as_type_to(&self, type_id: u32, types: &PortableRegistry, context: Context, out: &mut Vec<u8>) -> Result<(), Error> {
        let type_id = super::find_single_entry_with_same_repr(type_id, types);
        let ty = types
            .resolve(type_id)
            .ok_or_else(|| Error::new(context.clone(), ErrorKind::TypeNotFound(type_id)))?;

        match ty.type_def() {
            TypeDef::Variant(var) => {
                let vars = var.variants();
                let Some(v) = vars.iter().find(|v| v.name == self.name) else {
                    return Err(Error::new(context, ErrorKind::CannotFindVariant { name: self.name.to_string(), expected: type_id }));
                };
                v.index().encode_to(out);
                self.fields.encode_fields_to(v.fields(), type_id, types, context, out)
            },
            _ => {
                Err(Error::new(context, ErrorKind::WrongShape { actual: Kind::Str, expected: type_id }))
            }
        }
    }
}