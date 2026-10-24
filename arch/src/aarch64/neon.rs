//! The Advanced SIMD (NEON) integer intrinsics the Monty31 NEON backend and p3-field's NEON
//! helpers use.
//!
//! Each doc comment names the instruction the intrinsic compiles to and quotes the loop of its
//! *Operation* in Arm's pseudocode (ASL, Arm A-profile A64 ISA), which the body transcribes, with
//! the instruction's `esize`, `elements`, `unsigned` and similar fields fixed to the intrinsic's.
//! `Elem[v, e, esize]` is lane `e` of the lane array, lane 0 the least significant. `Int(x,
//! unsigned)`, `UInt` and `SInt` read a lane as an unbounded integer, which the bodies represent
//! in a wider Rust integer, and `x<h:l>` keeps those bits of it.
//!
//! Every shim is `unsafe fn`, like the AVX2 shims. The call sites call them inside `unsafe`
//! blocks. The intrinsics that take a shift amount reject one out of range at compile time; the
//! shims give every `N` a value, and agree with the intrinsic on the `N` it accepts.
#![allow(clippy::missing_safety_doc)]

use super::{int32x4_t, uint32x2_t, uint32x4_t, uint64x2_t};

/// `SignedSatQ(i, 32)`'s value: `i` clamped to `[-2^31, 2^31 - 1]`.
const fn signed_sat_q32(i: i64) -> i32 {
    if i > i32::MAX as i64 {
        i32::MAX
    } else if i < i32::MIN as i64 {
        i32::MIN
    } else {
        i as i32
    }
}

/// `vdupq_n_u32` (`DUP (general)`).
///
/// `element = X[n]<esize-1:0>; for e = 0 to elements-1  Elem[result, e, esize] = element;`
#[inline]
pub unsafe fn vdupq_n_u32(value: u32) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = value;
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vdupq_n_s32` (`DUP (general)`), as `vdupq_n_u32`.
#[inline]
pub unsafe fn vdupq_n_s32(value: i32) -> int32x4_t {
    let mut dst = [0i32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = value;
        e += 1;
    }
    int32x4_t(dst)
}

/// `vaddq_u32` (`ADD (vector)`).
///
/// `for e = 0 to elements-1  element1 = Elem[operand1, e, esize]; element2 = Elem[operand2, e,
/// esize]; Elem[result, e, esize] = element1 + element2;` (modulo `2^esize`).
#[inline]
pub unsafe fn vaddq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e].wrapping_add(b.0[e]);
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vaddq_s32` (`ADD (vector)`), as `vaddq_u32`: the bits are the same.
#[inline]
pub unsafe fn vaddq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    let mut dst = [0i32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e].wrapping_add(b.0[e]);
        e += 1;
    }
    int32x4_t(dst)
}

/// `vsubq_u32` (`SUB (vector)`).
///
/// `for e = 0 to elements-1  element1 = Elem[operand1, e, esize]; element2 = Elem[operand2, e,
/// esize]; Elem[result, e, esize] = element1 - element2;` (modulo `2^esize`).
#[inline]
pub unsafe fn vsubq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e].wrapping_sub(b.0[e]);
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vandq_u32` (`AND (vector)`).
///
/// `result = operand1 AND operand2;`
#[inline]
pub unsafe fn vandq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e] & b.0[e];
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vbicq_u32` (`BIC (vector, register)`).
///
/// `operand2 = NOT(operand2); result = operand1 AND operand2;`
#[inline]
pub unsafe fn vbicq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e] & !b.0[e];
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vminq_u32` (`UMIN`).
///
/// `for e = 0 to elements-1  element1 = Int(Elem[operand1, e, esize], unsigned); element2 =
/// Int(Elem[operand2, e, esize], unsigned); maxmin = Min(element1, element2); Elem[result, e,
/// esize] = maxmin<esize-1:0>;`
#[inline]
pub unsafe fn vminq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = if a.0[e] <= b.0[e] { a.0[e] } else { b.0[e] };
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vtstq_u32` (`CMTST`).
///
/// `for e = 0 to elements-1  element1 = Elem[operand1, e, esize]; element2 = Elem[operand2, e,
/// esize]; test_passed = !IsZero(element1 AND element2); Elem[result, e, esize] = if test_passed
/// then Ones(esize) else Zeros(esize);`
#[inline]
pub unsafe fn vtstq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = if a.0[e] & b.0[e] != 0 { u32::MAX } else { 0 };
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vceqzq_u32` (`CMEQ (zero)`).
///
/// `for e = 0 to elements-1  element = SInt(Elem[operand, e, esize]); test_passed = (element ==
/// 0); Elem[result, e, esize] = if test_passed then Ones(esize) else Zeros(esize);`
#[inline]
pub unsafe fn vceqzq_u32(a: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = if a.0[e] == 0 { u32::MAX } else { 0 };
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vcltq_u32` (`CMHI (register)`, operands swapped: `a < b` is `b > a`).
///
/// `for e = 0 to elements-1  element1 = Int(Elem[operand1, e, esize], unsigned); element2 =
/// Int(Elem[operand2, e, esize], unsigned); test_passed = element1 > element2; Elem[result, e,
/// esize] = if test_passed then Ones(esize) else Zeros(esize);`, with `operand1 = b`,
/// `operand2 = a`.
#[inline]
pub unsafe fn vcltq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = if b.0[e] > a.0[e] { u32::MAX } else { 0 };
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vcgeq_u32` (`CMHS (register)`).
///
/// `for e = 0 to elements-1  element1 = Int(Elem[operand1, e, esize], unsigned); element2 =
/// Int(Elem[operand2, e, esize], unsigned); test_passed = element1 >= element2; Elem[result, e,
/// esize] = if test_passed then Ones(esize) else Zeros(esize);`
#[inline]
pub unsafe fn vcgeq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = if a.0[e] >= b.0[e] { u32::MAX } else { 0 };
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vcltq_s32` (`CMGT (register)`, operands swapped: `a < b` is `b > a`).
///
/// `for e = 0 to elements-1  element1 = SInt(Elem[operand1, e, esize]); element2 =
/// SInt(Elem[operand2, e, esize]); test_passed = element1 > element2; Elem[result, e, esize] =
/// if test_passed then Ones(esize) else Zeros(esize);`, with `operand1 = b`, `operand2 = a`.
#[inline]
pub unsafe fn vcltq_s32(a: int32x4_t, b: int32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = if b.0[e] > a.0[e] { u32::MAX } else { 0 };
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vhaddq_u32` (`UHADD`).
///
/// `for e = 0 to elements-1  element1 = Int(Elem[operand1, e, esize], unsigned); element2 =
/// Int(Elem[operand2, e, esize], unsigned); sum = element1 + element2; Elem[result, e, esize] =
/// sum<esize:1>;`
#[inline]
pub unsafe fn vhaddq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        let sum = (a.0[e] as u64) + (b.0[e] as u64);
        dst[e] = (sum >> 1) as u32;
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vhsubq_s32` (`SHSUB`).
///
/// `for e = 0 to elements-1  element1 = Int(Elem[operand1, e, esize], unsigned = FALSE);
/// element2 = Int(Elem[operand2, e, esize], unsigned = FALSE); diff = element1 - element2;
/// Elem[result, e, esize] = diff<esize:1>;` (`diff<esize:1>` is `diff >> 1`, rounding down).
#[inline]
pub unsafe fn vhsubq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    let mut dst = [0i32; 4];
    let mut e = 0;
    while e < 4 {
        let diff = (a.0[e] as i64) - (b.0[e] as i64);
        dst[e] = (diff >> 1) as i32;
        e += 1;
    }
    int32x4_t(dst)
}

/// `vmulq_u32` (`MUL (vector)`).
///
/// `for e = 0 to elements-1  element1 = Elem[operand1, e, esize]; element2 = Elem[operand2, e,
/// esize]; product = (UInt(element1) * UInt(element2))<esize-1:0>; Elem[result, e, esize] =
/// product;`
#[inline]
pub unsafe fn vmulq_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e].wrapping_mul(b.0[e]);
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vmulq_s32` (`MUL (vector)`), as `vmulq_u32`: the low `esize` bits of a product do not
/// depend on the signedness.
#[inline]
pub unsafe fn vmulq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    let mut dst = [0i32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e].wrapping_mul(b.0[e]);
        e += 1;
    }
    int32x4_t(dst)
}

/// `vmlsq_u32` (`MLS (vector)`).
///
/// `for e = 0 to elements-1  element1 = Elem[operand1, e, esize]; element2 = Elem[operand2, e,
/// esize]; product = (UInt(element1) * UInt(element2))<esize-1:0>; Elem[result, e, esize] =
/// Elem[operand3, e, esize] - product;`, with `operand3 = a` (the accumulator), `operand1 = b`,
/// `operand2 = c`.
#[inline]
pub unsafe fn vmlsq_u32(a: uint32x4_t, b: uint32x4_t, c: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e].wrapping_sub(b.0[e].wrapping_mul(c.0[e]));
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vmlsq_n_u32` (`MLS (vector)` with every lane of `operand2` equal to `c`), as `vmlsq_u32`.
#[inline]
pub unsafe fn vmlsq_n_u32(a: uint32x4_t, b: uint32x4_t, c: u32) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e].wrapping_sub(b.0[e].wrapping_mul(c));
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vqdmulhq_s32` (`SQDMULH (vector)`).
///
/// `for e = 0 to elements-1  element1 = SInt(Elem[operand1, e, esize]); element2 =
/// SInt(Elem[operand2, e, esize]); product = (2 * element1 * element2) + round_const;
/// (Elem[result, e, esize], sat) = SignedSatQ(product >> esize, esize);`, with `round_const = 0`.
///
/// `element1 * element2` is at most `2^62` in absolute value, so it fits an `i64`; doubling it
/// may not (at `element1 = element2 = -2^31`). `(2 * p) >> 32` is `p >> 31`, both being
/// `floor(p / 2^31)`, so the body shifts the undoubled product by one less. The only product
/// that saturates is that one: `2^62 >> 31 = 2^31` clamps to `2^31 - 1`.
#[inline]
pub unsafe fn vqdmulhq_s32(a: int32x4_t, b: int32x4_t) -> int32x4_t {
    let mut dst = [0i32; 4];
    let mut e = 0;
    while e < 4 {
        let product = (a.0[e] as i64) * (b.0[e] as i64);
        dst[e] = signed_sat_q32(product >> 31);
        e += 1;
    }
    int32x4_t(dst)
}

/// `vshrq_n_u32::<N>` (`USHR`), for `1 <= N <= 32`.
///
/// `for e = 0 to elements-1  element = (Int(Elem[operand, e, esize], unsigned) + round_const) >>
/// shift; Elem[result, e, esize] = Elem[operand2, e, esize] + element<esize-1:0>;`, with
/// `round_const = 0`, `shift = N` and `operand2 = Zeros()`. A shift by 32 gives 0.
#[inline]
pub unsafe fn vshrq_n_u32<const N: i32>(a: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = if N as u32 >= 32 {
            0
        } else {
            a.0[e] >> N as u32
        };
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vsraq_n_u32::<N>` (`USRA`), for `1 <= N <= 32`: `USHR`'s loop with `operand2 = V[d]`, the
/// accumulator `a`, shifting `b`.
#[inline]
pub unsafe fn vsraq_n_u32<const N: i32>(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        let element = if N as u32 >= 32 {
            0
        } else {
            b.0[e] >> N as u32
        };
        dst[e] = a.0[e].wrapping_add(element);
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vshlq_n_u32::<N>` (`SHL`), for `0 <= N <= 31`.
///
/// `for e = 0 to elements-1  Elem[result, e, esize] = LSL(Elem[operand, e, esize], shift);`,
/// with `shift = N`.
#[inline]
pub unsafe fn vshlq_n_u32<const N: i32>(a: uint32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = if N as u32 >= 32 {
            0
        } else {
            a.0[e] << N as u32
        };
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vget_low_u32` (no instruction: the low 64 bits of the register).
///
/// `Vpart[n, 0]`: lanes 0 and 1.
#[inline]
pub unsafe fn vget_low_u32(a: uint32x4_t) -> uint32x2_t {
    uint32x2_t([a.0[0], a.0[1]])
}

/// `vmull_u32` (`UMULL`).
///
/// `for e = 0 to elements-1  element1 = Int(Elem[operand1, e, esize], unsigned); element2 =
/// Int(Elem[operand2, e, esize], unsigned); product = (element1 * element2)<2*esize-1:0>;
/// Elem[result, e, 2*esize] = product;`, with `esize = 32`, `elements = 2`.
#[inline]
pub unsafe fn vmull_u32(a: uint32x2_t, b: uint32x2_t) -> uint64x2_t {
    let mut dst = [0u64; 2];
    let mut e = 0;
    while e < 2 {
        dst[e] = (a.0[e] as u64) * (b.0[e] as u64);
        e += 1;
    }
    uint64x2_t(dst)
}

/// `vmull_high_u32` (`UMULL2`): `UMULL`'s loop on `Vpart[n, 1]`, lanes 2 and 3.
#[inline]
pub unsafe fn vmull_high_u32(a: uint32x4_t, b: uint32x4_t) -> uint64x2_t {
    let mut dst = [0u64; 2];
    let mut e = 0;
    while e < 2 {
        dst[e] = (a.0[2 + e] as u64) * (b.0[2 + e] as u64);
        e += 1;
    }
    uint64x2_t(dst)
}

/// `vmlal_u32` (`UMLAL`).
///
/// `for e = 0 to elements-1  element1 = Int(Elem[operand1, e, esize], unsigned); element2 =
/// Int(Elem[operand2, e, esize], unsigned); product = (element1 * element2)<2*esize-1:0>;
/// accum = Elem[operand3, e, 2*esize] + product; Elem[result, e, 2*esize] = accum;`, with
/// `operand3 = a` (the accumulator), `operand1 = b`, `operand2 = c`.
#[inline]
pub unsafe fn vmlal_u32(a: uint64x2_t, b: uint32x2_t, c: uint32x2_t) -> uint64x2_t {
    let mut dst = [0u64; 2];
    let mut e = 0;
    while e < 2 {
        dst[e] = a.0[e].wrapping_add((b.0[e] as u64) * (c.0[e] as u64));
        e += 1;
    }
    uint64x2_t(dst)
}

/// `vmlal_high_u32` (`UMLAL2`): `UMLAL`'s loop on `Vpart[n, 1]`, lanes 2 and 3 of `b` and `c`.
#[inline]
pub unsafe fn vmlal_high_u32(a: uint64x2_t, b: uint32x4_t, c: uint32x4_t) -> uint64x2_t {
    let mut dst = [0u64; 2];
    let mut e = 0;
    while e < 2 {
        dst[e] = a.0[e].wrapping_add((b.0[2 + e] as u64) * (c.0[2 + e] as u64));
        e += 1;
    }
    uint64x2_t(dst)
}

/// `vmlsl_u32` (`UMLSL`): `UMLAL`'s loop with `accum = Elem[operand3, e, 2*esize] - product`.
#[inline]
pub unsafe fn vmlsl_u32(a: uint64x2_t, b: uint32x2_t, c: uint32x2_t) -> uint64x2_t {
    let mut dst = [0u64; 2];
    let mut e = 0;
    while e < 2 {
        dst[e] = a.0[e].wrapping_sub((b.0[e] as u64) * (c.0[e] as u64));
        e += 1;
    }
    uint64x2_t(dst)
}

/// `vmlsl_high_u32` (`UMLSL2`): `UMLSL`'s loop on lanes 2 and 3 of `b` and `c`.
#[inline]
pub unsafe fn vmlsl_high_u32(a: uint64x2_t, b: uint32x4_t, c: uint32x4_t) -> uint64x2_t {
    let mut dst = [0u64; 2];
    let mut e = 0;
    while e < 2 {
        dst[e] = a.0[e].wrapping_sub((b.0[2 + e] as u64) * (c.0[2 + e] as u64));
        e += 1;
    }
    uint64x2_t(dst)
}

/// `vuzp1q_u32` (`UZP1`).
///
/// `zipped = operand2:operand1; for e = 0 to elements-1  Elem[result, e, esize] =
/// Elem[zipped, 2*e+part, esize];`, with `part = 0`.
#[inline]
pub unsafe fn vuzp1q_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    uint32x4_t([a.0[0], a.0[2], b.0[0], b.0[2]])
}

/// `vuzp2q_u32` (`UZP2`): `UZP1`'s loop with `part = 1`.
#[inline]
pub unsafe fn vuzp2q_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    uint32x4_t([a.0[1], a.0[3], b.0[1], b.0[3]])
}

/// `vtrn1q_u32` (`TRN1`).
///
/// `for p = 0 to pairs-1  Elem[result, 2*p+0, esize] = Elem[operand1, 2*p+part, esize];
/// Elem[result, 2*p+1, esize] = Elem[operand2, 2*p+part, esize];`, with `part = 0`.
#[inline]
pub unsafe fn vtrn1q_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    uint32x4_t([a.0[0], b.0[0], a.0[2], b.0[2]])
}

/// `vtrn2q_u32` (`TRN2`): `TRN1`'s loop with `part = 1`.
#[inline]
pub unsafe fn vtrn2q_u32(a: uint32x4_t, b: uint32x4_t) -> uint32x4_t {
    uint32x4_t([a.0[1], b.0[1], a.0[3], b.0[3]])
}

/// `vtrn1q_u64` (`TRN1`, `esize = 64`, one pair).
#[inline]
pub unsafe fn vtrn1q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    uint64x2_t([a.0[0], b.0[0]])
}

/// `vtrn2q_u64` (`TRN2`, `esize = 64`, one pair).
#[inline]
pub unsafe fn vtrn2q_u64(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    uint64x2_t([a.0[1], b.0[1]])
}

/// `vreinterpretq_s32_u32` (no instruction: the same 128 bits, read as signed lanes).
#[inline]
pub unsafe fn vreinterpretq_s32_u32(a: uint32x4_t) -> int32x4_t {
    let mut dst = [0i32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e] as i32;
        e += 1;
    }
    int32x4_t(dst)
}

/// `vreinterpretq_u32_s32` (no instruction: the same 128 bits, read as unsigned lanes).
#[inline]
pub unsafe fn vreinterpretq_u32_s32(a: int32x4_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut e = 0;
    while e < 4 {
        dst[e] = a.0[e] as u32;
        e += 1;
    }
    uint32x4_t(dst)
}

/// `vreinterpretq_u64_u32` (no instruction: the same 128 bits, as two 64-bit lanes). 64-bit
/// lane `k` is 32-bit lanes `2k` (low half) and `2k+1` (high half).
#[inline]
pub unsafe fn vreinterpretq_u64_u32(a: uint32x4_t) -> uint64x2_t {
    let mut dst = [0u64; 2];
    let mut k = 0;
    while k < 2 {
        dst[k] = (a.0[2 * k] as u64) | ((a.0[2 * k + 1] as u64) << 32);
        k += 1;
    }
    uint64x2_t(dst)
}

/// `vreinterpretq_u32_u64` (no instruction): the inverse of `vreinterpretq_u64_u32`.
#[inline]
pub unsafe fn vreinterpretq_u32_u64(a: uint64x2_t) -> uint32x4_t {
    let mut dst = [0u32; 4];
    let mut k = 0;
    while k < 2 {
        dst[2 * k] = a.0[k] as u32;
        dst[2 * k + 1] = (a.0[k] >> 32) as u32;
        k += 1;
    }
    uint32x4_t(dst)
}
