//! Models of `core::arch::x86_64`.

mod avx2;
mod avx512;
mod types;

pub use avx2::*;
pub use avx512::*;
pub use types::{
    M128i as __m128i, M256 as __m256, M256i as __m256i, M512 as __m512, M512d as __m512d,
    M512i as __m512i, Mmask8 as __mmask8, Mmask16 as __mmask16,
};
