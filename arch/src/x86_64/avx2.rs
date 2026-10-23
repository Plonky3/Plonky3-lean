//! The SSE and AVX/AVX2 integer intrinsics BabyBear's AVX2 backend uses.
//!
//! Each doc comment quotes the *Operation* section of Intel's Intrinsics Guide, which the body
//! transcribes. Bit ranges `[h:l]` of a 256-bit vector are lanes of the `[u32; 8]` array: lane `k`
//! holds bits `[32k+31 : 32k]`, so a 64-bit element `k` is lanes `2k` (low) and `2k+1` (high).
//!
//! Every shim is `unsafe fn`, like the intrinsics at the call sites, which call them inside
//! `unsafe` blocks.
#![allow(clippy::missing_safety_doc)]

use super::{__m128i, __m256, __m256i};

/// 64-bit element `k` of a 256-bit vector.
const fn lane64(a: &[u32; 8], k: usize) -> u64 {
    (a[2 * k] as u64) | ((a[2 * k + 1] as u64) << 32)
}

/// The low and high 32-bit lanes of a 64-bit value.
const fn split64(v: u64) -> (u32, u32) {
    (v as u32, (v >> 32) as u32)
}

/// `imm8[7:0]`, the immediate as the unsigned byte the instruction encodes.
const fn imm8(imm: i32) -> u32 {
    (imm as u32) & 0xff
}

/// `_mm256_add_epi32` (`vpaddd`).
///
/// `FOR j := 0 to 7; i := j*32; dst[i+31:i] := a[i+31:i] + b[i+31:i]; ENDFOR`
#[inline]
pub unsafe fn _mm256_add_epi32(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        dst[j] = a.0[j].wrapping_add(b.0[j]);
        j += 1;
    }
    __m256i(dst)
}

/// `_mm256_sub_epi32` (`vpsubd`).
///
/// `FOR j := 0 to 7; i := j*32; dst[i+31:i] := a[i+31:i] - b[i+31:i]; ENDFOR`
#[inline]
pub unsafe fn _mm256_sub_epi32(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        dst[j] = a.0[j].wrapping_sub(b.0[j]);
        j += 1;
    }
    __m256i(dst)
}

/// `_mm256_add_epi64` (`vpaddq`).
///
/// `FOR j := 0 to 3; i := j*64; dst[i+63:i] := a[i+63:i] + b[i+63:i]; ENDFOR`
#[inline]
pub unsafe fn _mm256_add_epi64(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut k = 0;
    while k < 4 {
        let (lo, hi) = split64(lane64(&a.0, k).wrapping_add(lane64(&b.0, k)));
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m256i(dst)
}

/// `_mm256_sub_epi64` (`vpsubq`).
///
/// `FOR j := 0 to 3; i := j*64; dst[i+63:i] := a[i+63:i] - b[i+63:i]; ENDFOR`
#[inline]
pub unsafe fn _mm256_sub_epi64(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut k = 0;
    while k < 4 {
        let (lo, hi) = split64(lane64(&a.0, k).wrapping_sub(lane64(&b.0, k)));
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m256i(dst)
}

/// `_mm256_min_epu32` (`vpminud`).
///
/// `FOR j := 0 to 7; i := j*32; dst[i+31:i] := MIN(a[i+31:i], b[i+31:i]); ENDFOR`
/// (unsigned comparison).
#[inline]
pub unsafe fn _mm256_min_epu32(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        dst[j] = if a.0[j] <= b.0[j] { a.0[j] } else { b.0[j] };
        j += 1;
    }
    __m256i(dst)
}

/// `_mm256_mul_epu32` (`vpmuludq`).
///
/// `FOR j := 0 to 3; i := j*64; dst[i+63:i] := a[i+31:i] * b[i+31:i]; ENDFOR`
/// (unsigned 32-bit by 32-bit, a 64-bit product).
#[inline]
pub unsafe fn _mm256_mul_epu32(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut k = 0;
    while k < 4 {
        let (lo, hi) = split64((a.0[2 * k] as u64) * (b.0[2 * k] as u64));
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m256i(dst)
}

/// `_mm256_mul_epi32` (`vpmuldq`).
///
/// `FOR j := 0 to 3; i := j*64; dst[i+63:i] := SignExtend64(a[i+31:i]) * SignExtend64(b[i+31:i]); ENDFOR`
#[inline]
pub unsafe fn _mm256_mul_epi32(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut k = 0;
    while k < 4 {
        let p = (a.0[2 * k] as i32 as i64) * (b.0[2 * k] as i32 as i64);
        let (lo, hi) = split64(p as u64);
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m256i(dst)
}

/// `_mm256_and_si256` (`vpand`).
///
/// `dst[255:0] := (a[255:0] AND b[255:0])`
#[inline]
pub unsafe fn _mm256_and_si256(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        dst[j] = a.0[j] & b.0[j];
        j += 1;
    }
    __m256i(dst)
}

/// `_mm256_madd_epi16` (`vpmaddwd`).
///
/// `FOR j := 0 to 7; i := j*32;`
/// `dst[i+31:i] := SignExtend32(a[i+31:i+16]*b[i+31:i+16]) + SignExtend32(a[i+15:i]*b[i+15:i]); ENDFOR`
/// (signed 16-bit products; the 32-bit sum wraps).
#[inline]
pub unsafe fn _mm256_madd_epi16(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        let a_lo = (a.0[j] & 0xffff) as u16 as i16 as i32;
        let a_hi = (a.0[j] >> 16) as u16 as i16 as i32;
        let b_lo = (b.0[j] & 0xffff) as u16 as i16 as i32;
        let b_hi = (b.0[j] >> 16) as u16 as i16 as i32;
        dst[j] = (a_hi * b_hi).wrapping_add(a_lo * b_lo) as u32;
        j += 1;
    }
    __m256i(dst)
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

/// `_mm256_maddubs_epi16` (`vpmaddubsw`).
///
/// `FOR j := 0 to 15; i := j*16;`
/// `dst[i+15:i] := Saturate16( a[i+15:i+8]*b[i+15:i+8] + a[i+7:i]*b[i+7:i] ); ENDFOR`
/// (`a`'s bytes unsigned, `b`'s signed).
#[inline]
pub unsafe fn _mm256_maddubs_epi16(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
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
    __m256i(dst)
}

/// `_mm256_sign_epi32` (`vpsignd`).
///
/// `FOR j := 0 to 7; i := j*32;`
/// `IF b[i+31:i] < 0; dst[i+31:i] := -(a[i+31:i]);`
/// `ELSE IF b[i+31:i] == 0; dst[i+31:i] := 0; ELSE; dst[i+31:i] := a[i+31:i]; FI; ENDFOR`
/// (signed comparison; the negation wraps).
#[inline]
pub unsafe fn _mm256_sign_epi32(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        let s = b.0[j] as i32;
        dst[j] = if s < 0 {
            (a.0[j] as i32).wrapping_neg() as u32
        } else if s == 0 {
            0
        } else {
            a.0[j]
        };
        j += 1;
    }
    __m256i(dst)
}

/// `_mm256_unpacklo_epi64` (`vpunpcklqdq`).
///
/// `DEFINE INTERLEAVE_QWORDS(src1[127:0], src2[127:0]) { dst[63:0] := src1[63:0];`
/// `dst[127:64] := src2[63:0] }`; `dst[127:0] := INTERLEAVE_QWORDS(a[127:0], b[127:0])`;
/// `dst[255:128] := INTERLEAVE_QWORDS(a[255:128], b[255:128])`
#[inline]
pub unsafe fn _mm256_unpacklo_epi64(a: __m256i, b: __m256i) -> __m256i {
    __m256i([
        a.0[0], a.0[1], b.0[0], b.0[1], a.0[4], a.0[5], b.0[4], b.0[5],
    ])
}

/// `_mm256_unpackhi_epi64` (`vpunpckhqdq`).
///
/// `DEFINE INTERLEAVE_HIGH_QWORDS(src1[127:0], src2[127:0]) { dst[63:0] := src1[127:64];`
/// `dst[127:64] := src2[127:64] }`; `dst[127:0] := INTERLEAVE_HIGH_QWORDS(a[127:0], b[127:0])`;
/// `dst[255:128] := INTERLEAVE_HIGH_QWORDS(a[255:128], b[255:128])`
#[inline]
pub unsafe fn _mm256_unpackhi_epi64(a: __m256i, b: __m256i) -> __m256i {
    __m256i([
        a.0[2], a.0[3], b.0[2], b.0[3], a.0[6], a.0[7], b.0[6], b.0[7],
    ])
}

/// `_mm256_blend_epi32` (`vpblendd`).
///
/// `FOR j := 0 to 7; i := j*32;`
/// `IF imm8[j]; dst[i+31:i] := b[i+31:i]; ELSE; dst[i+31:i] := a[i+31:i]; FI; ENDFOR`
#[inline]
pub unsafe fn _mm256_blend_epi32<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        dst[j] = if (imm8(IMM8) >> j) & 1 == 1 {
            b.0[j]
        } else {
            a.0[j]
        };
        j += 1;
    }
    __m256i(dst)
}

/// `_mm256_permute2x128_si256` (`vperm2i128`).
///
/// `DEFINE SELECT4(src1, src2, control) { CASE(control[1:0]) OF 0: tmp[127:0] := src1[127:0];`
/// `1: tmp[127:0] := src1[255:128]; 2: tmp[127:0] := src2[127:0]; 3: tmp[127:0] := src2[255:128];`
/// `ESAC; IF control[3]; tmp[127:0] := 0; FI; RETURN tmp[127:0] }`;
/// `dst[127:0] := SELECT4(a[255:0], b[255:0], imm8[3:0])`;
/// `dst[255:128] := SELECT4(a[255:0], b[255:0], imm8[7:4])`
#[inline]
pub unsafe fn _mm256_permute2x128_si256<const IMM8: i32>(a: __m256i, b: __m256i) -> __m256i {
    let mut dst = [0u32; 8];
    let mut half = 0;
    while half < 2 {
        let control = (imm8(IMM8) >> (4 * half)) & 0xf;
        let src = if control & 2 == 0 { a.0 } else { b.0 };
        let base = 4 * ((control & 1) as usize);
        let mut l = 0;
        while l < 4 {
            dst[4 * half + l] = if control & 8 == 0 { src[base + l] } else { 0 };
            l += 1;
        }
        half += 1;
    }
    __m256i(dst)
}

/// `_mm256_slli_epi32` (`vpslld`).
///
/// `FOR j := 0 to 7; i := j*32; IF imm8[7:0] > 31; dst[i+31:i] := 0;`
/// `ELSE; dst[i+31:i] := ZeroExtend32(a[i+31:i] << imm8[7:0]); FI; ENDFOR`
#[inline]
pub unsafe fn _mm256_slli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    let s = imm8(IMM8);
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        dst[j] = if s > 31 { 0 } else { a.0[j] << s };
        j += 1;
    }
    __m256i(dst)
}

/// `_mm256_srli_epi32` (`vpsrld`).
///
/// `FOR j := 0 to 7; i := j*32; IF imm8[7:0] > 31; dst[i+31:i] := 0;`
/// `ELSE; dst[i+31:i] := ZeroExtend32(a[i+31:i] >> imm8[7:0]); FI; ENDFOR`
#[inline]
pub unsafe fn _mm256_srli_epi32<const IMM8: i32>(a: __m256i) -> __m256i {
    let s = imm8(IMM8);
    let mut dst = [0u32; 8];
    let mut j = 0;
    while j < 8 {
        dst[j] = if s > 31 { 0 } else { a.0[j] >> s };
        j += 1;
    }
    __m256i(dst)
}

/// `_mm256_slli_epi64` (`vpsllq`).
///
/// `FOR j := 0 to 3; i := j*64; IF imm8[7:0] > 63; dst[i+63:i] := 0;`
/// `ELSE; dst[i+63:i] := ZeroExtend64(a[i+63:i] << imm8[7:0]); FI; ENDFOR`
#[inline]
pub unsafe fn _mm256_slli_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    let s = imm8(IMM8);
    let mut dst = [0u32; 8];
    let mut k = 0;
    while k < 4 {
        let v = if s > 63 { 0 } else { lane64(&a.0, k) << s };
        let (lo, hi) = split64(v);
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m256i(dst)
}

/// `_mm256_srli_epi64` (`vpsrlq`).
///
/// `FOR j := 0 to 3; i := j*64; IF imm8[7:0] > 63; dst[i+63:i] := 0;`
/// `ELSE; dst[i+63:i] := ZeroExtend64(a[i+63:i] >> imm8[7:0]); FI; ENDFOR`
#[inline]
pub unsafe fn _mm256_srli_epi64<const IMM8: i32>(a: __m256i) -> __m256i {
    let s = imm8(IMM8);
    let mut dst = [0u32; 8];
    let mut k = 0;
    while k < 4 {
        let v = if s > 63 { 0 } else { lane64(&a.0, k) >> s };
        let (lo, hi) = split64(v);
        dst[2 * k] = lo;
        dst[2 * k + 1] = hi;
        k += 1;
    }
    __m256i(dst)
}

/// `_mm256_set1_epi32` (a sequence; `vpbroadcastd`).
///
/// `FOR j := 0 to 7; i := j*32; dst[i+31:i] := a[31:0]; ENDFOR`
#[inline]
pub unsafe fn _mm256_set1_epi32(a: i32) -> __m256i {
    __m256i([a as u32; 8])
}

/// `_mm256_setr_epi32` (a sequence).
///
/// `dst[31:0] := e7; dst[63:32] := e6; … dst[255:224] := e0`, Intel naming the arguments
/// `e7, …, e0` in order. Rust names them `e0, …, e7` in the same order, so lane `j` is the
/// `j`-th argument.
#[inline]
#[allow(clippy::too_many_arguments)]
pub unsafe fn _mm256_setr_epi32(
    e0: i32,
    e1: i32,
    e2: i32,
    e3: i32,
    e4: i32,
    e5: i32,
    e6: i32,
    e7: i32,
) -> __m256i {
    __m256i([
        e0 as u32, e1 as u32, e2 as u32, e3 as u32, e4 as u32, e5 as u32, e6 as u32, e7 as u32,
    ])
}

/// `_mm256_setzero_si256` (`vpxor`).
///
/// `dst[MAX:0] := 0`
#[inline]
pub unsafe fn _mm256_setzero_si256() -> __m256i {
    __m256i([0u32; 8])
}

/// `_mm256_castsi256_ps`: a reinterpretation, no instruction. "This intrinsic is only used for
/// compilation and does not generate any instructions, thus it has zero latency."
#[inline]
pub unsafe fn _mm256_castsi256_ps(a: __m256i) -> __m256 {
    __m256(a.0)
}

/// `_mm256_castps_si256`: a reinterpretation, no instruction (as for `_mm256_castsi256_ps`).
#[inline]
pub unsafe fn _mm256_castps_si256(a: __m256) -> __m256i {
    __m256i(a.0)
}

/// `_mm256_movehdup_ps` (`vmovshdup`).
///
/// `dst[31:0] := a[63:32]; dst[63:32] := a[63:32]; dst[95:64] := a[127:96];`
/// `dst[127:96] := a[127:96]; dst[159:128] := a[191:160]; dst[191:160] := a[191:160];`
/// `dst[223:192] := a[255:224]; dst[255:224] := a[255:224]` (a move: bit patterns are copied).
#[inline]
pub unsafe fn _mm256_movehdup_ps(a: __m256) -> __m256 {
    __m256([
        a.0[1], a.0[1], a.0[3], a.0[3], a.0[5], a.0[5], a.0[7], a.0[7],
    ])
}

/// `_mm_add_epi32` (`paddd`).
///
/// `FOR j := 0 to 3; i := j*32; dst[i+31:i] := a[i+31:i] + b[i+31:i]; ENDFOR`
#[inline]
pub unsafe fn _mm_add_epi32(a: __m128i, b: __m128i) -> __m128i {
    let mut dst = [0u32; 4];
    let mut j = 0;
    while j < 4 {
        dst[j] = a.0[j].wrapping_add(b.0[j]);
        j += 1;
    }
    __m128i(dst)
}

/// `_mm_sub_epi32` (`psubd`).
///
/// `FOR j := 0 to 3; i := j*32; dst[i+31:i] := a[i+31:i] - b[i+31:i]; ENDFOR`
#[inline]
pub unsafe fn _mm_sub_epi32(a: __m128i, b: __m128i) -> __m128i {
    let mut dst = [0u32; 4];
    let mut j = 0;
    while j < 4 {
        dst[j] = a.0[j].wrapping_sub(b.0[j]);
        j += 1;
    }
    __m128i(dst)
}

/// `_mm_min_epu32` (`pminud`, SSE4.1).
///
/// `FOR j := 0 to 3; i := j*32; dst[i+31:i] := MIN(a[i+31:i], b[i+31:i]); ENDFOR`
/// (unsigned comparison).
#[inline]
pub unsafe fn _mm_min_epu32(a: __m128i, b: __m128i) -> __m128i {
    let mut dst = [0u32; 4];
    let mut j = 0;
    while j < 4 {
        dst[j] = if a.0[j] <= b.0[j] { a.0[j] } else { b.0[j] };
        j += 1;
    }
    __m128i(dst)
}

/// `_mm_set1_epi32` (a sequence).
///
/// `FOR j := 0 to 3; i := j*32; dst[i+31:i] := a[31:0]; ENDFOR`
#[inline]
pub unsafe fn _mm_set1_epi32(a: i32) -> __m128i {
    __m128i([a as u32; 4])
}
