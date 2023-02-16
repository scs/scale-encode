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
struct Foo { }

#[derive(EncodeAsType)]
struct Foo2;

#[derive(EncodeAsType)]
struct Foo3();

fn can_encode_as_type<T: EncodeAsType>() {}

fn main() {
    // assert that the trait is implemented:
    can_encode_as_type::<Foo>();
    can_encode_as_type::<Foo2>();
    can_encode_as_type::<Foo3>();
}