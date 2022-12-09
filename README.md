## Everscale types &emsp; [![everscale-types: rustc 1.65+]][Rust 1.65] [![Workflow badge]][Workflow]

[everscale-types: rustc 1.65+]: https://img.shields.io/badge/rustc-1.65+-lightgray.svg

[Rust 1.65]: https://blog.rust-lang.org/2022/11/03/Rust-1.65.0.html

[Workflow badge]: https://img.shields.io/github/workflow/status/broxus/everscale-types/master

[Workflow]: https://github.com/broxus/everscale-types/actions?query=workflow%3Amaster

> Status: WIP

A set of primitive types and utilities for the Everscale blockchain.

Heavily inspired by [`ton-labs-types`](https://github.com/tonlabs/ton-labs-types),
but with much more emphasis on speed.

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
cargo +nightly fuzz run boc_arc_decode_pair -j 12
cargo +nightly fuzz run boc_arc_decode -j 12
cargo +nightly fuzz run boc_rc_decode_pair -j 12
cargo +nightly fuzz run boc_rc_decode -j 12
```

## License

Licensed under either of

* Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)
* MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.
