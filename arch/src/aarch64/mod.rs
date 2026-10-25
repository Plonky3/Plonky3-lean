//! Models of `core::arch::aarch64`.

mod neon;
mod types;

pub use neon::*;
pub use types::{
    I32x4 as int32x4_t, U32x2 as uint32x2_t, U32x4 as uint32x4_t, U64x2 as uint64x2_t,
};
