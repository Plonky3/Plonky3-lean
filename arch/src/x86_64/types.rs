//! The vector types, as lane arrays with the same size and layout as the hardware registers.
//!
//! `mod.rs` exports each under its `core::arch` name (`M256i` as `__m256i`). The definitions
//! are named without the leading `__`, which the generated Lean would otherwise carry into
//! names that mathlib's naming linter rejects.
//!
//! Like the `core::arch` types, they implement `Clone`, `Copy` and `Debug`, and not
//! `PartialEq`. `Debug` is implemented by hand rather than derived, since the extractor fails
//! on the derived impl.

use core::fmt;

/// `__m256i`, a 256-bit integer vector: eight 32-bit lanes, lane 0 the least significant.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct M256i(pub [u32; 8]);

/// `__m128i`, a 128-bit integer vector: four 32-bit lanes, lane 0 the least significant.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct M128i(pub [u32; 4]);

/// `__m256`, a 256-bit vector of eight single-precision floats, kept as their bit patterns.
/// The shims that take one only move lanes, so no floating-point arithmetic is modelled.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct M256(pub [u32; 8]);

/// The lanes, least significant first. Some backends' types derive `Debug` over a vector.
macro_rules! debug_lanes {
    ($t:ident, $name:literal) => {
        impl fmt::Debug for $t {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}({:#010x?})", $name, self.0)
            }
        }
    };
}

debug_lanes!(M256i, "__m256i");
debug_lanes!(M128i, "__m128i");
debug_lanes!(M256, "__m256");
