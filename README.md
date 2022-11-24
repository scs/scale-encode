# scale-encode

`scale-encode` builds on `parity-scale-codec`. `parity-scale-codec` provides an `Encode` trait
which allows types to SCALE encode themselves with no external information. `scale-encode` provides an
[`EncodeAsType`] trait which allows types to decide how to encode themselves based on the desired
target type.