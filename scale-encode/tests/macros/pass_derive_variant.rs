// Copyright (C) 2023 Parity Technologies (UK) Ltd. (admin@parity.io)
// This file is a part of the scale-encode crate.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//         http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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