//! Verification-only models of the `core::arch` intrinsics Plonky3's SIMD backends use.
//!
//! Each shim has the name and signature of its `core::arch` counterpart, over vector types that
//! are `repr(transparent)` lane arrays, and a body transcribed from the vendor's pseudocode
//! (Intel's *Operation* section, Arm's ASL). Under `cfg(hax_backend_lean)` the backends import
//! this crate instead of `core::arch`, so the extractor translates the shims as ordinary Rust.
//!
//! Each shim is trusted: it is reviewed against the pseudocode and differentially tested against
//! the real intrinsic (`tests/`). The bodies use only `while` loops, integer arithmetic and fixed
//! arrays, so that the extractor translates them.
#![no_std]

pub mod aarch64;
pub mod x86_64;
