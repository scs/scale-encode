use scale_encode::EncodeAsType;

// Single field named struct
#[derive(EncodeAsType)]
// this should lead to no issues:
#[encode_as_type(path = "::scale_encode")]
struct Foo {
    some_field: u8
}

// Single field unnamed struct
#[derive(EncodeAsType)]
struct Foo2(String);

// Multi field unnamed struct
#[derive(EncodeAsType)]
struct Foo3(String, bool, u8, u8);

// Multi field named struct (using names commonly
// used i nthe trait definition):
#[derive(EncodeAsType)]
struct Foo4 {
    ty: u8,
    out: bool,
    context: String,
    types: u64
}

fn can_encode_as_type<T: EncodeAsType>() {}

fn main() {
    // assert that the trait is implemented:
    can_encode_as_type::<Foo>();
    can_encode_as_type::<Foo2>();
    can_encode_as_type::<Foo3>();
    can_encode_as_type::<Foo4>();
}