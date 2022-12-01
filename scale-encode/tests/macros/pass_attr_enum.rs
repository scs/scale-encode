use scale_encode::{
    EncodeAsType,
    encode_as_type
};

#[encode_as_type]
#[encode_as_type(
    crate_path = "::scale_encode",
    type_path = "foreign_mod::Foo"
)]
enum Foo<T> {
    Named { field: u8, other: String, more: bool },
    Unit,
    Named2 { other: T },
    Unnamed(u8)
}

pub mod foreign_mod {
    pub enum Foo<T> {
        Named { field: u8, other: String, more: bool },
        // make sure no fields are handled ok:
        Unit,
        // make sure one named field handled properly:
        Named2 { other: T },
        // make sure one unnamed field handled properly:
        Unnamed(u8)
    }
}

fn can_encode_as_type<T: EncodeAsType>() {}

fn main() {
    // assert that the trait is implemented:
    can_encode_as_type::<foreign_mod::Foo<u64>>();
}