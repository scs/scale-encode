use scale_encode::{
    encode_as_type,
    EncodeAsType
};

// Implement EncodeAsType on a foreign type
// by providing the shape of the type to an attr macro:
#[encode_as_type]
#[encode_as_type(type_path = "foreign_type::Foo")]
struct Foo {
    ty: u8,
    out: bool,
    context: String,
    types: u64
}

pub mod foreign_type {
    pub struct Foo {
        // fields need to be public to be able to derive
        // the macro on this type.
        pub ty: u8,
        pub out: bool,
        pub context: String,
        pub types: u64
    }
}

fn can_encode_as_type<T: EncodeAsType>() {}

fn main() {
    // assert that the trait is implemented on the foreign type:
    can_encode_as_type::<foreign_type::Foo>();
}