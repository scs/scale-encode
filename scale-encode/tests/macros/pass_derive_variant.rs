use scale_encode::EncodeAsType;

#[derive(EncodeAsType)]
// this should lead to no issues:
#[encode_as_type(crate_path = "::scale_encode")]
enum Foo {
    Named { field: u8, other: String, more: bool },
    // make sure no fields are handled ok:
    Unit,
    // make sure one named field handled properly:
    Named2 { other: bool },
    // make sure one unnamed field handled properly:
    Unnamed(u8)
}

fn can_encode_as_type<T: EncodeAsType>() {}

fn main() {
    // assert that the trait is implemented as expected:
    can_encode_as_type::<Foo>();
}