<p align="center">
  <a href="https://github.com/venom-blockchain/developer-program">
    <img src="https://raw.githubusercontent.com/venom-blockchain/developer-program/main/vf-dev-program.png" alt="Logo" width="366.8" height="146.4">
  </a>
</p>

# Everscale types &emsp; [![crates-io-batch]][crates-io-link] [![docs-badge]][docs-url] [![rust-version-badge]][rust-version-link] [![workflow-badge]][workflow-link]

[crates-io-batch]: https://img.shields.io/crates/v/everscale-types.svg

[crates-io-link]: https://crates.io/crates/everscale-types

[docs-badge]: https://docs.rs/everscale-types/badge.svg

[docs-url]: https://docs.rs/everscale-types

[rust-version-badge]: https://img.shields.io/badge/rustc-1.65+-lightgray.svg

[rust-version-link]: https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html

[workflow-badge]: https://img.shields.io/github/actions/workflow/status/broxus/everscale-types/master.yml?branch=master

[workflow-link]: https://github.com/broxus/everscale-types/actions?query=workflow%3Amaster

> Status: WIP

## About

A set of primitive types and utilities for the Everscale blockchain.

Heavily inspired by [`ton-labs-types`](https://github.com/tonlabs/ton-labs-types),
but with much more emphasis on speed.

## Basic usage

Get `Cell` from `Vec<u8>` representation of bytes
```rust
use everscale_types::boc::Boc;

let cell: Cell = Boc::decode(bytes)?;
```

Encode any model e.g.`MerkleProof` to `base64` BOC representation and vice versa
```rust
use everscale_types::boc::BocRepr;

let cell = MerkleProof::create_for_cell(cell.as_ref(), EMPTY_CELL_HASH)
            .build()
            .unwrap();

let encoded = BocRepr::encode_base64(&cell).unwrap();

let decoded = Boc::decode_base64(encoded)?.as_ref().parse::<MerkleProof>()?:
```

Get specific everscale type from `Cell`
```rust
use everscale_types::models::BlockProof;

let proof: BlockProof = cell.parse::<BlockProof>()?;
```
Same usage for virtualized cell
```rust
use everscale_types::prelude::DynCell;
use everscale_types::models::Block;

let virt_cell: &DynCell = cell.virtualize();
let block = virt_cell.parse::<Block>()?;
```

You can also use `CellBuilder` to create any `Cell`
```rust
let mut builder = CellBuilder::new();
builder.store_bit_one()?;
builder.store_u32(100u32)?
builder.store_slice(slice)?;
builder.store_raw(&[0xdd, 0x55], 10)?;

// store references to another cells
builder.store_reference(cell)?;
builder.store_reference(another_cell)?;

let final_cell = builder.build()?;
```

## Development

### How to bench

```bash
cargo bench boc
cargo bench dict
```

### How to miri check

```bash
# Add Miri component
rustup +nightly component add miri

# Run all tests with Miri
cargo +nightly miri test
```

### How to fuzz

```bash
# Install fuzzer
cargo install cargo-fuzz

# Run any of the fuzzer targets
cargo +nightly fuzz run boc_decode -j 12
cargo +nightly fuzz run boc_decode_encode -j 12
cargo +nightly fuzz run boc_decode_pair -j 12
cargo +nightly fuzz run boc_dict -j 12
cargo +nightly fuzz run boc_message -j 12
```

## Contributing

We welcome contributions to the project! If you notice any issues or errors, feel free to open an issue or submit a pull request.

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <https://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or <https://opensource.org/licenses/MIT>)

at your option.
