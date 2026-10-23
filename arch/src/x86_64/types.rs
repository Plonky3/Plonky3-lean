//! The vector types, as lane arrays with the same size and layout as the hardware registers.
//!
//! No `Debug` derive: the extractor fails on the derived impl.
#![allow(non_camel_case_types)]

/// A 256-bit integer vector: eight 32-bit lanes, lane 0 the least significant.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct __m256i(pub [u32; 8]);

/// A 128-bit integer vector: four 32-bit lanes, lane 0 the least significant.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct __m128i(pub [u32; 4]);

/// A 256-bit vector of eight single-precision floats, kept as their bit patterns. The shims that
/// take one only move lanes, so no floating-point arithmetic is modelled.
#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct __m256(pub [u32; 8]);
