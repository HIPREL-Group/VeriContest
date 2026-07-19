//! Dependency vehicle for the Verus test-input generators.
//!
//! This crate is never imported. It exists so that `cargo build` resolves and
//! compiles `serde` and `serde_json` into `target/debug/deps`, which
//! `run_generators.py` then passes to Verus as `--extern serde` /
//! `--extern serde_json` when compiling each problem's `tests/gen.rs`. Verus has
//! no package manager of its own, so this is how the generators get JSON output.
//!
//! The toolchain pin in `rust-toolchain.toml` must match Verus's bundled rustc,
//! or the resulting rlibs will not link.
