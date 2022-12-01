use scale_encode::EncodeAsType;

struct NotEncodeAsType;

// Enums with generic params can impl EncodeAsType.
#[derive(EncodeAsType)]
enum Bar<T, U, V> {
    Wibble(bool, T, U, V),
    Wobble
}

// This impls EncodeAsType ok; we set no default trait bounds.
#[derive(EncodeAsType)]
#[encode_as_type(trait_bounds = "")]
enum NoTraitBounds<T> {
    Wibble(std::marker::PhantomData<T>),
}

// Structs (and const bounds) impl EncodeAsType OK.
#[derive(EncodeAsType)]
struct MyStruct<const V: usize, Bar: Clone + PartialEq> {
    array: [Bar; V]
}

fn can_encode_as_type<T: EncodeAsType>() {}

fn main() {
    // assert that the trait is implemented as expected:
    can_encode_as_type::<Bar<u8, String, bool>>();
    can_encode_as_type::<NoTraitBounds<NotEncodeAsType>>();
    can_encode_as_type::<MyStruct<16, u64>>();
}