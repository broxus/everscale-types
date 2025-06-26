# tycho-types &emsp; [![crates-io-batch]][crates-io-link] [![docs-badge]][docs-url] [![rust-version-badge]][rust-version-link] [![workflow-badge]][workflow-link]

[crates-io-batch]: https://img.shields.io/crates/v/tycho-types.svg
[crates-io-link]: https://crates.io/crates/tycho-types
[docs-badge]: https://docs.rs/tycho-types/badge.svg
[docs-url]: https://docs.rs/tycho-types
[rust-version-badge]: https://img.shields.io/badge/rustc-1.85+-lightgray.svg
[rust-version-link]: https://blog.rust-lang.org/2025/02/20/Rust-1.85.0/
[workflow-badge]: https://img.shields.io/github/actions/workflow/status/broxus/tycho-types/master.yml?branch=master
[workflow-link]: https://github.com/broxus/tycho-types/actions?query=workflow%3Amaster

> Status: WIP

## About

A set of primitive types and utilities for the Tycho node.

## Basic usage

Decode `Cell` from bytes using the BOC (Bag Of Cells) format:
```rust
use tycho_types::boc::Boc;

let cell: Cell = Boc::decode(bytes)?;
```

Encode TLB model e.g.`MerkleProof`:
```rust
use tycho_types::boc::BocRepr;

let proof = MerkleProof::create_for_cell(cell.as_ref(), some_filter).build()?;

let encoded = BocRepr::encode_base64(proof)?;
let decoded = BocRepr::decode_base64(encoded)?:
```

Parse TLB type from `Cell`:
```rust
use tycho_types::models::BlockProof;

let proof: BlockProof = cell.parse::<BlockProof>()?;
```

Parse TLB type from proof cell (partially pruned):
```rust
use tycho_types::cell::DynCell;
use tycho_types::models::Block;

let virt_cell: &DynCell = proof.virtualize();
let block = virt_cell.parse::<Block>()?;
```

Use `CellBuilder` to create any `Cell`:
```rust
let mut builder = CellBuilder::new();
builder.store_bit_one()?;
builder.store_u32(100u32)?
builder.store_slice(slice)?;
builder.store_raw(&[0xdd, 0x55], 10)?;

// store references to another cells
builder.store_reference(cell)?;
builder.store_reference(another_cell)?;

let final_cell: Cell = builder.build()?;

// === or ===
let other_cell: Cell = CellBuilder::build_from((
    true,
    100u32,
    cell,
    another_cell,
))?;
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
