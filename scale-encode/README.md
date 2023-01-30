# scale-encode

Provides an `EncodeAsType` trait, and impls on common types, which builds on `parity-scale-codec::Encode` and allows more flexible encoding of types based on some provided type information in a `scale_info::PortableRegistry`.