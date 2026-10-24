//! Models of `core::arch::x86_64`.

mod avx2;
mod types;

pub use avx2::*;
pub use types::{M128i as __m128i, M256 as __m256, M256i as __m256i};
