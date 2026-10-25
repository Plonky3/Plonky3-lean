//! The vector types, as lane arrays with the same size and layout as the hardware registers.
//!
//! `mod.rs` exports each under its `core::arch` name (`U32x4` as `uint32x4_t`). The definitions
//! are named in Rust's type-name style, as the x86_64 ones are. Lane 0 is the least significant,
//! as on a little-endian AArch64 target.
//!
//! Like the `core::arch` types, they implement `Clone`, `Copy` and `Debug`, and not
//! `PartialEq`. `Debug` is implemented by hand rather than derived, since the extractor fails
//! on the derived impl.

use core::fmt;

/// `uint32x4_t`, a 128-bit vector of four unsigned 32-bit lanes.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct U32x4(pub [u32; 4]);

/// `int32x4_t`, a 128-bit vector of four signed 32-bit lanes.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct I32x4(pub [i32; 4]);

/// `uint64x2_t`, a 128-bit vector of two unsigned 64-bit lanes.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct U64x2(pub [u64; 2]);

/// `uint32x2_t`, a 64-bit vector of two unsigned 32-bit lanes.
#[derive(Clone, Copy)]
#[repr(transparent)]
pub struct U32x2(pub [u32; 2]);

/// The lanes, least significant first. Some backends' types derive `Debug` over a vector.
macro_rules! debug_lanes {
    ($t:ident, $name:literal) => {
        impl fmt::Debug for $t {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, "{}({:#x?})", $name, self.0)
            }
        }
    };
}

debug_lanes!(U32x4, "uint32x4_t");
debug_lanes!(I32x4, "int32x4_t");
debug_lanes!(U64x2, "uint64x2_t");
debug_lanes!(U32x2, "uint32x2_t");
