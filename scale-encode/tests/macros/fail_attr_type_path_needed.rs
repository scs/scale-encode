use scale_encode::encode_as_type;

// A type_path is needed to know what type to
// generate the impl for when attr macro is used.
#[encode_as_type]
struct Foo {
    ty: u8,
    out: bool,
    context: String,
    types: u64
}

fn main() {}