//! The AVX-512 intrinsics BabyBear's AVX-512 backend uses: AVX-512F, and the few from
//! AVX-512BW (`madd`, `maddubs`), AVX-512VL (the masked 256-bit forms) and AVX-512VBMI2
//! (`shrdi`) that its code names.
//!
//! Each doc comment quotes the *Operation* section of Intel's Intrinsics Guide, which the body
//! transcribes. Bit ranges `[h:l]` of a 512-bit vector are lanes of the `[u32; 16]` array: lane
//! `k` holds bits `[32k+31 : 32k]`, so a 64-bit element `k` is lanes `2k` (low) and `2k+1`
//! (high). `__m512d` is eight 64-bit lanes, lane `k` bits `[64k+63 : 64k]`.
//!
//! A mask (`__mmask16`, `__mmask8`) is an unsigned integer whose bit `j`, `k[j]`, belongs to
//! element `j`. The masked forms write element `j` of the result only where `k[j]` is set, and
//! elsewhere take it from `src` (`mask_`) or zero it (`maskz_`). The comparisons write bit `j`
//! of the mask from element `j`, and leave the bits above the element count zero
//! (`k[MAX:16] := 0`).
//!
//! These shims are reviewed against the pseudocode but not yet tested against the hardware:
//! `tests/avx512.rs` runs only on a CPU with AVX-512, which no machine or runner available to
//! this project guarantees (TRUST.md).
//!
//! Every shim is `unsafe fn`, like the intrinsics at the call sites, which call them inside
//! `unsafe` blocks.
#![allow(clippy::missing_safety_doc)]

use super::{__m256, __m256i, __m512, __m512d, __m512i, __mmask8, __mmask16};

/// 64-bit element `k` of a 512-bit integer vector.
const fn lane64(a: &[u32; 16], k: usize) -> u64 {
    (a[2 * k] as u64) | ((a[2 * k + 1] as u64) << 32)
}

/// The low and high 32-bit lanes of a 64-bit value.
const fn split64(v: u64) -> (u32, u32) {
    (v as u32, (v >> 32) as u32)
}

/// `imm8[7:0]`, a signed immediate as the unsigned byte the instruction encodes.
const fn imm8(imm: i32) -> u32 {
    (imm as u32) & 0xff
}

/// `imm8[7:0]`, for the intrinsics whose immediate `core::arch` types as a `u32`.
const fn imm8u(imm: u32) -> u32 {
    imm & 0xff
}

/// `k[j]`, bit `j` of a 16-bit mask.
const fn bit16(k: __mmask16, j: usize) -> bool {
    (k >> j) & 1 == 1
}

/// `k[j]`, bit `j` of an 8-bit mask.
const fn bit8(k: __mmask8, j: usize) -> bool {
    (k >> j) & 1 == 1
}

// ---------------------------------------------------------------------------------------------
// Lane-wise arithmetic
// ---------------------------------------------------------------------------------------------

/// `_mm512_add_epi32` (`vpaddd`).
///
/// `FOR j := 0 to 15; i := j*32; dst[i+31:i] := a[i+31:i] + b[i+31:i]; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_add_epi32(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = a.0[j].wrapping_add(b.0[j]);
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_sub_epi32` (`vpsubd`).
///
/// `FOR j := 0 to 15; i := j*32; dst[i+31:i] := a[i+31:i] - b[i+31:i]; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_sub_epi32(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = a.0[j].wrapping_sub(b.0[j]);
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_add_epi64` (`vpaddq`).
///
/// `FOR j := 0 to 7; i := j*64; dst[i+63:i] := a[i+63:i] + b[i+63:i]; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_add_epi64(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut k = 0;
    while k < 8 {
        let (lo, hi) = split64(lane64(&a.0, k).wrapping_add(lane64(&b.0, k)));
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m512i(dst)
}

/// `_mm512_sub_epi64` (`vpsubq`).
///
/// `FOR j := 0 to 7; i := j*64; dst[i+63:i] := a[i+63:i] - b[i+63:i]; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_sub_epi64(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut k = 0;
    while k < 8 {
        let (lo, hi) = split64(lane64(&a.0, k).wrapping_sub(lane64(&b.0, k)));
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m512i(dst)
}

/// `_mm512_min_epu32` (`vpminud`).
///
/// `FOR j := 0 to 15; i := j*32; dst[i+31:i] := MIN(a[i+31:i], b[i+31:i]); ENDFOR;`
/// `dst[MAX:512] := 0` (unsigned comparison).
#[inline]
pub unsafe fn _mm512_min_epu32(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = if a.0[j] <= b.0[j] { a.0[j] } else { b.0[j] };
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_mul_epu32` (`vpmuludq`).
///
/// `FOR j := 0 to 7; i := j*64; dst[i+63:i] := a[i+31:i] * b[i+31:i]; ENDFOR; dst[MAX:512] := 0`
/// (unsigned 32-bit by 32-bit, a 64-bit product).
#[inline]
pub unsafe fn _mm512_mul_epu32(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut k = 0;
    while k < 8 {
        let (lo, hi) = split64((a.0[2 * k] as u64) * (b.0[2 * k] as u64));
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m512i(dst)
}

/// `_mm512_mul_epi32` (`vpmuldq`).
///
/// `FOR j := 0 to 7; i := j*64;`
/// `dst[i+63:i] := SignExtend64(a[i+31:i]) * SignExtend64(b[i+31:i]); ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_mul_epi32(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut k = 0;
    while k < 8 {
        let p = (a.0[2 * k] as i32 as i64) * (b.0[2 * k] as i32 as i64);
        let (lo, hi) = split64(p as u64);
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m512i(dst)
}

/// `_mm512_and_si512` (`vpandq`).
///
/// `dst[511:0] := (a[511:0] AND b[511:0]); dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_and_si512(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = a.0[j] & b.0[j];
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_madd_epi16` (`vpmaddwd`, AVX-512BW).
///
/// `FOR j := 0 to 15; i := j*32;`
/// `dst[i+31:i] := SignExtend32(a[i+31:i+16]*b[i+31:i+16]) + SignExtend32(a[i+15:i]*b[i+15:i]);`
/// `ENDFOR; dst[MAX:512] := 0` (signed 16-bit products; the 32-bit sum wraps).
#[inline]
pub unsafe fn _mm512_madd_epi16(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        let a_lo = (a.0[j] & 0xffff) as u16 as i16 as i32;
        let a_hi = (a.0[j] >> 16) as u16 as i16 as i32;
        let b_lo = (b.0[j] & 0xffff) as u16 as i16 as i32;
        let b_hi = (b.0[j] >> 16) as u16 as i16 as i32;
        dst[j] = (a_hi * b_hi).wrapping_add(a_lo * b_lo) as u32;
        j += 1;
    }
    __m512i(dst)
}

/// `Saturate16`: a signed value clamped to `[-2^15, 2^15 - 1]`.
const fn saturate16(x: i32) -> i32 {
    if x > 32767 {
        32767
    } else if x < -32768 {
        -32768
    } else {
        x
    }
}

/// `_mm512_maddubs_epi16` (`vpmaddubsw`, AVX-512BW).
///
/// `FOR j := 0 to 31; i := j*16;`
/// `dst[i+15:i] := Saturate16( a[i+15:i+8]*b[i+15:i+8] + a[i+7:i]*b[i+7:i] ); ENDFOR;`
/// `dst[MAX:512] := 0` (`a`'s bytes unsigned, `b`'s signed). The 16-bit element `j` is half
/// `j % 2` of lane `j / 2`.
#[inline]
pub unsafe fn _mm512_maddubs_epi16(a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        let mut word = 0u32;
        let mut h = 0;
        while h < 2 {
            let s0 = 16 * h;
            let s1 = 16 * h + 8;
            let a0 = ((a.0[j] >> s0) & 0xff) as i32;
            let a1 = ((a.0[j] >> s1) & 0xff) as i32;
            let b0 = ((b.0[j] >> s0) & 0xff) as u8 as i8 as i32;
            let b1 = ((b.0[j] >> s1) & 0xff) as u8 as i8 as i32;
            let r = saturate16(a1 * b1 + a0 * b0);
            word |= ((r as u32) & 0xffff) << s0;
            h += 1;
        }
        dst[j] = word;
        j += 1;
    }
    __m512i(dst)
}

// ---------------------------------------------------------------------------------------------
// Shifts by an immediate
// ---------------------------------------------------------------------------------------------

/// `_mm512_srli_epi32` (`vpsrld`).
///
/// `FOR j := 0 to 15; i := j*32; IF imm8[7:0] > 31; dst[i+31:i] := 0;`
/// `ELSE; dst[i+31:i] := ZeroExtend32(a[i+31:i] >> imm8[7:0]); FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_srli_epi32<const IMM8: u32>(a: __m512i) -> __m512i {
    let s = imm8u(IMM8);
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = if s > 31 { 0 } else { a.0[j] >> s };
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_slli_epi64` (`vpsllq`).
///
/// `FOR j := 0 to 7; i := j*64; IF imm8[7:0] > 63; dst[i+63:i] := 0;`
/// `ELSE; dst[i+63:i] := ZeroExtend64(a[i+63:i] << imm8[7:0]); FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_slli_epi64<const IMM8: u32>(a: __m512i) -> __m512i {
    let s = imm8u(IMM8);
    let mut dst = [0u32; 16];
    let mut k = 0;
    while k < 8 {
        let v = if s > 63 { 0 } else { lane64(&a.0, k) << s };
        let (lo, hi) = split64(v);
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m512i(dst)
}

/// `_mm512_mask_slli_epi32` (`vpslld` with a merge mask).
///
/// `FOR j := 0 to 15; i := j*32; IF k[j]; IF imm8[7:0] > 31; dst[i+31:i] := 0;`
/// `ELSE; dst[i+31:i] := ZeroExtend32(a[i+31:i] << imm8[7:0]); FI;`
/// `ELSE; dst[i+31:i] := src[i+31:i]; FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_mask_slli_epi32<const IMM8: u32>(
    src: __m512i,
    k: __mmask16,
    a: __m512i,
) -> __m512i {
    let s = imm8u(IMM8);
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = if bit16(k, j) {
            if s > 31 { 0 } else { a.0[j] << s }
        } else {
            src.0[j]
        };
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_shrdi_epi64` (`vpshrdq`, AVX-512VBMI2).
///
/// `FOR j := 0 to 7; i := j*64;`
/// `tmp[127:0] := ((b[i+63:i] << 64)[127:0] | a[i+63:i]) >> imm8[5:0];`
/// `dst[i+63:i] := tmp[63:0]; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_shrdi_epi64<const IMM8: i32>(a: __m512i, b: __m512i) -> __m512i {
    let s = imm8(IMM8) & 0x3f;
    let mut dst = [0u32; 16];
    let mut k = 0;
    while k < 8 {
        let tmp = (((lane64(&b.0, k) as u128) << 64) | (lane64(&a.0, k) as u128)) >> s;
        let (lo, hi) = split64(tmp as u64);
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m512i(dst)
}

// ---------------------------------------------------------------------------------------------
// Masked arithmetic
// ---------------------------------------------------------------------------------------------

/// `_mm512_mask_add_epi32` (`vpaddd` with a merge mask).
///
/// `FOR j := 0 to 15; i := j*32; IF k[j]; dst[i+31:i] := a[i+31:i] + b[i+31:i];`
/// `ELSE; dst[i+31:i] := src[i+31:i]; FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_mask_add_epi32(src: __m512i, k: __mmask16, a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = if bit16(k, j) {
            a.0[j].wrapping_add(b.0[j])
        } else {
            src.0[j]
        };
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_mask_sub_epi32` (`vpsubd` with a merge mask).
///
/// `FOR j := 0 to 15; i := j*32; IF k[j]; dst[i+31:i] := a[i+31:i] - b[i+31:i];`
/// `ELSE; dst[i+31:i] := src[i+31:i]; FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_mask_sub_epi32(src: __m512i, k: __mmask16, a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = if bit16(k, j) {
            a.0[j].wrapping_sub(b.0[j])
        } else {
            src.0[j]
        };
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_maskz_sub_epi32` (`vpsubd` with a zeroing mask).
///
/// `FOR j := 0 to 15; i := j*32; IF k[j]; dst[i+31:i] := a[i+31:i] - b[i+31:i];`
/// `ELSE; dst[i+31:i] := 0; FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_maskz_sub_epi32(k: __mmask16, a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = if bit16(k, j) {
            a.0[j].wrapping_sub(b.0[j])
        } else {
            0
        };
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_mask_sub_epi64` (`vpsubq` with a merge mask).
///
/// `FOR j := 0 to 7; i := j*64; IF k[j]; dst[i+63:i] := a[i+63:i] - b[i+63:i];`
/// `ELSE; dst[i+63:i] := src[i+63:i]; FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_mask_sub_epi64(src: __m512i, k: __mmask8, a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 8 {
        let v = if bit8(k, j) {
            lane64(&a.0, j).wrapping_sub(lane64(&b.0, j))
        } else {
            lane64(&src.0, j)
        };
        let (lo, hi) = split64(v);
        dst[2 * j] = lo;
        dst[2 * j + 1] = hi;
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_mask_blend_epi32` (`vpblendmd`).
///
/// `FOR j := 0 to 15; i := j*32; IF k[j]; dst[i+31:i] := b[i+31:i];`
/// `ELSE; dst[i+31:i] := a[i+31:i]; FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_mask_blend_epi32(k: __mmask16, a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = if bit16(k, j) { b.0[j] } else { a.0[j] };
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_mask_blend_epi64` (`vpblendmq`).
///
/// `FOR j := 0 to 7; i := j*64; IF k[j]; dst[i+63:i] := b[i+63:i];`
/// `ELSE; dst[i+63:i] := a[i+63:i]; FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_mask_blend_epi64(k: __mmask8, a: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 8 {
        let src = if bit8(k, j) { b.0 } else { a.0 };
        dst[2 * j] = src[2 * j];
        dst[2 * j + 1] = src[2 * j + 1];
        j += 1;
    }
    __m512i(dst)
}

/// `_mm256_mask_add_epi32` (`vpaddd` with a merge mask, AVX-512VL).
///
/// `FOR j := 0 to 7; i := j*32; IF k[j]; dst[i+31:i] := a[i+31:i] + b[i+31:i];`
/// `ELSE; dst[i+31:i] := src[i+31:i]; FI; ENDFOR; dst[MAX:256] := 0`
#[inline]
pub unsafe fn _mm256_mask_add_epi32(src: __m256i, k: __mmask8, a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        dst[j] = if bit8(k, j) {
            a.0[j].wrapping_add(b.0[j])
        } else {
            src.0[j]
        };
        j += 1;
    }
    __m256i(dst)
}

// ---------------------------------------------------------------------------------------------
// Comparisons into a mask
// ---------------------------------------------------------------------------------------------

/// `_mm512_cmplt_epu32_mask` (`vpcmpud`, predicate `_MM_CMPINT_LT`).
///
/// `FOR j := 0 to 15; i := j*32; k[j] := ( a[i+31:i] < b[i+31:i] ) ? 1 : 0; ENDFOR;`
/// `k[MAX:16] := 0` (unsigned comparison).
#[inline]
pub unsafe fn _mm512_cmplt_epu32_mask(a: __m512i, b: __m512i) -> __mmask16 {
    let mut k: __mmask16 = 0;
    let mut j = 0;
    while j < 16 {
        if a.0[j] < b.0[j] {
            k |= 1 << j;
        }
        j += 1;
    }
    k
}

/// `_mm512_cmplt_epi32_mask` (`vpcmpd`, predicate `_MM_CMPINT_LT`).
///
/// `FOR j := 0 to 15; i := j*32; k[j] := ( a[i+31:i] < b[i+31:i] ) ? 1 : 0; ENDFOR;`
/// `k[MAX:16] := 0` (signed comparison).
#[inline]
pub unsafe fn _mm512_cmplt_epi32_mask(a: __m512i, b: __m512i) -> __mmask16 {
    let mut k: __mmask16 = 0;
    let mut j = 0;
    while j < 16 {
        if (a.0[j] as i32) < (b.0[j] as i32) {
            k |= 1 << j;
        }
        j += 1;
    }
    k
}

/// `_mm512_cmple_epu32_mask` (`vpcmpud`, predicate `_MM_CMPINT_LE`).
///
/// `FOR j := 0 to 15; i := j*32; k[j] := ( a[i+31:i] <= b[i+31:i] ) ? 1 : 0; ENDFOR;`
/// `k[MAX:16] := 0` (unsigned comparison).
#[inline]
pub unsafe fn _mm512_cmple_epu32_mask(a: __m512i, b: __m512i) -> __mmask16 {
    let mut k: __mmask16 = 0;
    let mut j = 0;
    while j < 16 {
        if a.0[j] <= b.0[j] {
            k |= 1 << j;
        }
        j += 1;
    }
    k
}

/// `_mm512_cmple_epu64_mask` (`vpcmpuq`, predicate `_MM_CMPINT_LE`).
///
/// `FOR j := 0 to 7; i := j*64; k[j] := ( a[i+63:i] <= b[i+63:i] ) ? 1 : 0; ENDFOR;`
/// `k[MAX:8] := 0` (unsigned comparison).
#[inline]
pub unsafe fn _mm512_cmple_epu64_mask(a: __m512i, b: __m512i) -> __mmask8 {
    let mut k: __mmask8 = 0;
    let mut j = 0;
    while j < 8 {
        if lane64(&a.0, j) <= lane64(&b.0, j) {
            k |= 1 << j;
        }
        j += 1;
    }
    k
}

/// `_mm512_test_epi32_mask` (`vptestmd`).
///
/// `FOR j := 0 to 15; i := j*32; k[j] := ((a[i+31:i] AND b[i+31:i]) != 0) ? 1 : 0; ENDFOR;`
/// `k[MAX:16] := 0`
#[inline]
pub unsafe fn _mm512_test_epi32_mask(a: __m512i, b: __m512i) -> __mmask16 {
    let mut k: __mmask16 = 0;
    let mut j = 0;
    while j < 16 {
        if a.0[j] & b.0[j] != 0 {
            k |= 1 << j;
        }
        j += 1;
    }
    k
}

/// `_mm256_cmplt_epu32_mask` (`vpcmpud`, predicate `_MM_CMPINT_LT`, AVX-512VL).
///
/// `FOR j := 0 to 7; i := j*32; k[j] := ( a[i+31:i] < b[i+31:i] ) ? 1 : 0; ENDFOR;`
/// `k[MAX:8] := 0` (unsigned comparison).
#[inline]
pub unsafe fn _mm256_cmplt_epu32_mask(a: __m256i, b: __m256i) -> __mmask8 {
    let mut k: __mmask8 = 0;
    let mut j = 0;
    while j < 8 {
        if a.0[j] < b.0[j] {
            k |= 1 << j;
        }
        j += 1;
    }
    k
}

// ---------------------------------------------------------------------------------------------
// Moves, shuffles and permutations
// ---------------------------------------------------------------------------------------------

/// `_mm512_movehdup_ps` (`vmovshdup`).
///
/// `dst[31:0] := a[63:32]; dst[63:32] := a[63:32]; dst[95:64] := a[127:96];`
/// `dst[127:96] := a[127:96]; … dst[479:448] := a[511:480]; dst[511:480] := a[511:480];`
/// `dst[MAX:512] := 0` (a move: bit patterns are copied).
#[inline]
pub unsafe fn _mm512_movehdup_ps(a: __m512) -> __m512 {
    __m512([
        a.0[1], a.0[1], a.0[3], a.0[3], a.0[5], a.0[5], a.0[7], a.0[7], a.0[9], a.0[9], a.0[11],
        a.0[11], a.0[13], a.0[13], a.0[15], a.0[15],
    ])
}

/// `_mm512_mask_movehdup_ps` (`vmovshdup` with a merge mask).
///
/// `tmp[31:0] := a[63:32]; tmp[63:32] := a[63:32]; tmp[95:64] := a[127:96];`
/// `tmp[127:96] := a[127:96]; … tmp[479:448] := a[511:480]; tmp[511:480] := a[511:480];`
/// `FOR j := 0 to 15; i := j*32; IF k[j]; dst[i+31:i] := tmp[i+31:i];`
/// `ELSE; dst[i+31:i] := src[i+31:i]; FI; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_mask_movehdup_ps(src: __m512, k: __mmask16, a: __m512) -> __m512 {
    let tmp = [
        a.0[1], a.0[1], a.0[3], a.0[3], a.0[5], a.0[5], a.0[7], a.0[7], a.0[9], a.0[9], a.0[11],
        a.0[11], a.0[13], a.0[13], a.0[15], a.0[15],
    ];
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        dst[j] = if bit16(k, j) { tmp[j] } else { src.0[j] };
        j += 1;
    }
    __m512(dst)
}

/// `_mm256_mask_movehdup_ps` (`vmovshdup` with a merge mask, AVX-512VL).
///
/// `tmp[31:0] := a[63:32]; tmp[63:32] := a[63:32]; tmp[95:64] := a[127:96];`
/// `tmp[127:96] := a[127:96]; tmp[159:128] := a[191:160]; tmp[191:160] := a[191:160];`
/// `tmp[223:192] := a[255:224]; tmp[255:224] := a[255:224];`
/// `FOR j := 0 to 7; i := j*32; IF k[j]; dst[i+31:i] := tmp[i+31:i];`
/// `ELSE; dst[i+31:i] := src[i+31:i]; FI; ENDFOR; dst[MAX:256] := 0`
#[inline]
pub unsafe fn _mm256_mask_movehdup_ps(src: __m256, k: __mmask8, a: __m256) -> __m256 {
    let tmp = [
        a.0[1], a.0[1], a.0[3], a.0[3], a.0[5], a.0[5], a.0[7], a.0[7],
    ];
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        dst[j] = if bit8(k, j) { tmp[j] } else { src.0[j] };
        j += 1;
    }
    __m256(dst)
}

/// `_mm512_shuffle_epi32` (`vpshufd`).
///
/// `DEFINE SELECT4(src, control) { CASE(control[1:0]) OF 0: tmp[31:0] := src[31:0];`
/// `1: tmp[31:0] := src[63:32]; 2: tmp[31:0] := src[95:64]; 3: tmp[31:0] := src[127:96];`
/// `ESAC; RETURN tmp[31:0] }`; for each 128-bit lane `l` (bits `[128l+127 : 128l]`),
/// `dst[128l+31:128l] := SELECT4(a[128l+127:128l], imm8[1:0])`, …,
/// `dst[128l+127:128l+96] := SELECT4(a[128l+127:128l], imm8[7:6])`; `dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_shuffle_epi32<const MASK: i32>(a: __m512i) -> __m512i {
    let control = imm8(MASK);
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        let lane = j / 4;
        let e = j % 4;
        let sel = ((control >> (2 * e)) & 3) as usize;
        dst[j] = a.0[4 * lane + sel];
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_shuffle_i64x2` (`vshufi64x2`).
///
/// `DEFINE SELECT4(src, control) { CASE(control[1:0]) OF 0: tmp[127:0] := src[127:0];`
/// `1: tmp[127:0] := src[255:128]; 2: tmp[127:0] := src[383:256]; 3: tmp[127:0] := src[511:384];`
/// `ESAC; RETURN tmp[127:0] }`; `dst[127:0] := SELECT4(a[511:0], imm8[1:0])`;
/// `dst[255:128] := SELECT4(a[511:0], imm8[3:2])`; `dst[383:256] := SELECT4(b[511:0], imm8[5:4])`;
/// `dst[511:384] := SELECT4(b[511:0], imm8[7:6])`; `dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_shuffle_i64x2<const MASK: i32>(a: __m512i, b: __m512i) -> __m512i {
    let control = imm8(MASK);
    let mut dst = [0u32; 16];
    let mut l = 0;
    while l < 4 {
        let src = if l < 2 { a.0 } else { b.0 };
        let sel = ((control >> (2 * l)) & 3) as usize;
        let mut e = 0;
        while e < 4 {
            dst[4 * l + e] = src[4 * sel + e];
            e += 1;
        }
        l += 1;
    }
    __m512i(dst)
}

/// `_mm512_shuffle_pd` (`vshufpd`).
///
/// `dst[63:0] := (imm8[0] == 0) ? a[63:0] : a[127:64];`
/// `dst[127:64] := (imm8[1] == 0) ? b[63:0] : b[127:64];`
/// `dst[191:128] := (imm8[2] == 0) ? a[191:128] : a[255:192];`
/// `dst[255:192] := (imm8[3] == 0) ? b[191:128] : b[255:192];`
/// `dst[319:256] := (imm8[4] == 0) ? a[319:256] : a[383:320];`
/// `dst[383:320] := (imm8[5] == 0) ? b[319:256] : b[383:320];`
/// `dst[447:384] := (imm8[6] == 0) ? a[447:384] : a[511:448];`
/// `dst[511:448] := (imm8[7] == 0) ? b[447:384] : b[511:448]; dst[MAX:512] := 0`
///
/// So element `j` comes from `a` for even `j` and `b` for odd `j`, from the pair of elements
/// `2 * (j / 2)` and `2 * (j / 2) + 1`, the higher one where `imm8[j]` is set.
#[inline]
pub unsafe fn _mm512_shuffle_pd<const MASK: i32>(a: __m512d, b: __m512d) -> __m512d {
    let control = imm8(MASK);
    let mut dst = [0u64; 8];
    let mut j = 0;
    while j < 8 {
        let src = if j % 2 == 0 { a.0 } else { b.0 };
        let base = 2 * (j / 2);
        dst[j] = if (control >> j) & 1 == 0 {
            src[base]
        } else {
            src[base + 1]
        };
        j += 1;
    }
    __m512d(dst)
}

/// `_mm512_permutex2var_epi32` (`vpermt2d` / `vpermi2d`).
///
/// `FOR j := 0 to 15; i := j*32; off := idx[i+3:i]*32;`
/// `dst[i+31:i] := idx[i+4] ? b[off+31:off] : a[off+31:off]; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_permutex2var_epi32(a: __m512i, idx: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 16 {
        let off = (idx.0[j] & 0xf) as usize;
        dst[j] = if (idx.0[j] >> 4) & 1 == 1 {
            b.0[off]
        } else {
            a.0[off]
        };
        j += 1;
    }
    __m512i(dst)
}

/// `_mm512_permutex2var_epi64` (`vpermt2q` / `vpermi2q`).
///
/// `FOR j := 0 to 7; i := j*64; off := idx[i+2:i]*64;`
/// `dst[i+63:i] := idx[i+3] ? b[off+63:off] : a[off+63:off]; ENDFOR; dst[MAX:512] := 0`
///
/// `idx[i+3:i]` are the low bits of the 64-bit element, in lane `2j`.
#[inline]
pub unsafe fn _mm512_permutex2var_epi64(a: __m512i, idx: __m512i, b: __m512i) -> __m512i {
    let mut dst = [0u32; 16];
    let mut j = 0;
    while j < 8 {
        let sel = idx.0[2 * j];
        let off = (sel & 0x7) as usize;
        let src = if (sel >> 3) & 1 == 1 { b.0 } else { a.0 };
        dst[2 * j] = src[2 * off];
        dst[2 * j + 1] = src[2 * off + 1];
        j += 1;
    }
    __m512i(dst)
}

// ---------------------------------------------------------------------------------------------
// Constructors and casts
// ---------------------------------------------------------------------------------------------

/// `_mm512_set1_epi32` (`vpbroadcastd`).
///
/// `FOR j := 0 to 15; i := j*32; dst[i+31:i] := a[31:0]; ENDFOR; dst[MAX:512] := 0`
#[inline]
pub unsafe fn _mm512_set1_epi32(a: i32) -> __m512i {
    __m512i([a as u32; 16])
}

/// `_mm512_setzero_epi32` (`vpxorq`).
///
/// `dst[MAX:0] := 0`
#[inline]
pub unsafe fn _mm512_setzero_epi32() -> __m512i {
    __m512i([0u32; 16])
}

/// `_mm512_castsi512_ps`: a reinterpretation, no instruction. "This intrinsic is only used for
/// compilation and does not generate any instructions, thus it has zero latency."
#[inline]
pub unsafe fn _mm512_castsi512_ps(a: __m512i) -> __m512 {
    __m512(a.0)
}

/// `_mm512_castps_si512`: a reinterpretation, no instruction (as for `_mm512_castsi512_ps`).
#[inline]
pub unsafe fn _mm512_castps_si512(a: __m512) -> __m512i {
    __m512i(a.0)
}

/// `_mm512_castsi512_pd`: a reinterpretation, no instruction (as for `_mm512_castsi512_ps`).
/// Element `k` of the result is the 64-bit element `k`, lanes `2k` (low) and `2k + 1` (high).
#[inline]
pub unsafe fn _mm512_castsi512_pd(a: __m512i) -> __m512d {
    let mut dst = [0u64; 8];
    let mut k = 0;
    while k < 8 {
        dst[k] = lane64(&a.0, k);
        k += 1;
    }
    __m512d(dst)
}

/// `_mm512_castpd_si512`: a reinterpretation, no instruction (as for `_mm512_castsi512_ps`).
/// Element `k` becomes lanes `2k` (low half) and `2k + 1` (high half).
#[inline]
pub unsafe fn _mm512_castpd_si512(a: __m512d) -> __m512i {
    let mut dst = [0u32; 16];
    let mut k = 0;
    while k < 8 {
        let (lo, hi) = split64(a.0[k]);
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m512i(dst)
}

/// `_mm512_castsi512_si256`: a reinterpretation, no instruction (as for
/// `_mm512_castsi512_ps`). The result is the low 256 bits, `dst[255:0] := a[255:0]`.
#[inline]
pub unsafe fn _mm512_castsi512_si256(a: __m512i) -> __m256i {
    __m256i([
        a.0[0], a.0[1], a.0[2], a.0[3], a.0[4], a.0[5], a.0[6], a.0[7],
    ])
}
