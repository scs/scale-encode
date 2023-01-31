use crate::{ EncodeAsType, error::{ Error, ErrorKind, Kind } };
use scale_info::TypeDef;

impl EncodeAsType for scale_bits::Bits {
    fn encode_as_type_to(&self, type_id: u32, types: &scale_info::PortableRegistry, out: &mut Vec<u8>) -> Result<(), crate::Error> {
        let type_id = super::find_single_entry_with_same_repr(type_id, types);
        let ty = types
            .resolve(type_id)
            .ok_or_else(|| Error::new(ErrorKind::TypeNotFound(type_id)))?;

        if let TypeDef::BitSequence(ty) = ty.type_def() {
            let Ok(format) = scale_bits::Format::from_metadata(ty, types) else {
                return Err(wrong_shape(type_id))
            };

            scale_bits::encode_using_format_to(self.iter(), format, out);
            Ok(())
        } else {
            Err(wrong_shape(type_id))
        }
    }
}

fn wrong_shape(type_id: u32) -> Error {
    Error::new(ErrorKind::WrongShape { actual: Kind::BitSequence, expected: type_id })
}