//! Differential tests: every AVX-512 shim against the `core::arch` intrinsic it models.
//!
//! As for AVX2 (`tests/avx2.rs`): the inputs are lanes drawn from edge values and from a
//! fixed-seed generator, and every shim that takes an immediate is checked at all 256 values of
//! its 8-bit immediate. The masked shims are also checked at every mask: all 256 of an 8-bit
//! mask on every case, and all 65536 of a 16-bit mask on a few vectors, besides a random mask
//! per case. The comparisons are also checked on equal and nearly equal inputs.
//!
//! The tests need an x86_64 build with the AVX-512 features the backend's code names:
//!
//!     RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512vl,+avx512vbmi2" \
//!         cargo test --release --test avx512 --target <x86_64 triple>
//!
//! Elsewhere the file compiles to nothing. A CPU without these features cannot run them: each
//! test then checks the CPU first (`is_x86_feature_detected!`), says once on stderr that it is
//! skipped, and passes without running anything. So a pass here is evidence only where that
//! line was not printed.
#![cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "avx512bw",
    target_feature = "avx512vl",
    target_feature = "avx512vbmi2"
))]

use core::arch::x86_64 as hw;
use core::mem::transmute;
use std::io::Write;
use std::sync::atomic::{AtomicBool, Ordering};

use p3_arch_shims::x86_64 as shim;

/// Whether this CPU, and the OS, support every feature the tests are compiled for.
///
/// `is_x86_feature_detected!` cannot say: it answers `true` without asking the CPU for a
/// feature enabled at compile time, as these are. So this reads CPUID and XCR0 itself: leaf 7
/// for AVX-512F (EBX bit 16), BW (EBX bit 30), VL (EBX bit 31) and VBMI2 (ECX bit 6), and XCR0
/// for the OS saving the SSE, AVX, opmask and ZMM state (bits 1, 2, 5, 6 and 7).
#[cfg(not(miri))]
fn has_avx512() -> bool {
    unsafe {
        if hw::__cpuid(0).eax < 7 || hw::__cpuid(1).ecx & (1 << 27) == 0 {
            return false;
        }
        if hw::_xgetbv(0) & 0xe6 != 0xe6 {
            return false;
        }
        let l7 = hw::__cpuid_count(7, 0);
        l7.ebx & (1 << 16) != 0
            && l7.ebx & (1 << 30) != 0
            && l7.ebx & (1 << 31) != 0
            && l7.ecx & (1 << 6) != 0
    }
}

/// Under Miri, the CPU is the interpreter, which has the features `RUSTFLAGS` enables.
#[cfg(miri)]
fn has_avx512() -> bool {
    true
}

static SKIP_NOTICE: AtomicBool = AtomicBool::new(false);

/// Returns from the test, which then passes, when the CPU lacks AVX-512. The notice goes
/// straight to stderr, past the test harness's output capture, once per run. It writes a fixed
/// string through std's precompiled code, since this crate's own code may use AVX-512.
macro_rules! require_avx512 {
    () => {
        if !has_avx512() {
            if !SKIP_NOTICE.swap(true, Ordering::Relaxed) {
                let _ = std::io::stderr().write_all(
                    b"skipped: no AVX-512 (avx512f, avx512bw, avx512vl, avx512vbmi2) on this \
                      CPU; the AVX-512 shims are not tested here\n",
                );
            }
            return;
        }
    };
}

const EDGES: [u32; 26] = [
    0,
    1,
    2,
    0x7f,
    0x80,
    0xff,
    0x100,
    0x7fff,
    0x8000,
    0xffff,
    0x1_0000,
    0x7800_0000, // BabyBear P - 1
    0x7800_0001, // BabyBear P
    0x7800_0002, // BabyBear P + 1
    0x7f00_0001, // KoalaBear P
    0x7fff_fffe,
    0x7fff_ffff,
    0x8000_0000,
    0x8000_0001,
    0x8800_0001, // BabyBear MU
    0xf000_0000,
    0xfffe_ffff,
    0xffff_0000,
    0xffff_fffe,
    0xffff_ffff,
    0x5555_5555,
];

/// Under Miri, which interprets `core::arch`'s own Rust implementation of each intrinsic
/// rather than running the instruction, the tests run on fewer cases.
const MIRI: bool = cfg!(miri);

const RANDOM: usize = if MIRI { 20 } else { 100_000 };
/// Random cases per immediate, for the shims checked at all 256 immediates.
const RANDOM_PER_IMM: usize = 1_000;
/// Cases per mask, for the 8-bit masked shims checked at all 256 masks.
const RANDOM_PER_MASK8: usize = 1_000;
/// Under Miri, the cases per immediate and per 8-bit mask: random ones only.
const MIRI_CASES: usize = 2;
/// Equal and nearly equal pairs, for the comparisons.
const NEAR: usize = if MIRI { 4 } else { 1_000 };
/// Every pair of edge values is a case, or under Miri every `EDGE_STRIDE`-th.
const EDGE_STRIDE: usize = if MIRI { 53 } else { 1 };
/// The 16-bit masks checked on a few vectors: all of them, or under Miri every
/// `MASK16_STRIDE`-th.
const MASK16_STRIDE: usize = if MIRI { 997 } else { 1 };

type L16 = [u32; 16];
type L8 = [u32; 8];

/// A xorshift generator: fixed seed, so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// A lane: an edge value a quarter of the time, otherwise uniform.
    fn lane(&mut self) -> u32 {
        let r = self.next();
        if r & 3 == 0 {
            EDGES[((r >> 2) % EDGES.len() as u64) as usize]
        } else {
            (r >> 32) as u32
        }
    }

    fn lanes16(&mut self) -> L16 {
        core::array::from_fn(|_| self.lane())
    }

    fn mask16(&mut self) -> u16 {
        (self.next() >> 17) as u16
    }
}

/// Pairs of 16-lane inputs: each pair of edge values, in the even lanes, with edge values
/// rotating through the odd lanes; equal and nearly equal pairs, for the comparisons; then
/// `random` mixed vectors.
fn cases(random: usize) -> Vec<(L16, L16)> {
    let n = EDGES.len();
    let mut out = Vec::new();
    for (i, &x) in EDGES.iter().enumerate() {
        for (j, &y) in EDGES.iter().enumerate() {
            let a = core::array::from_fn(|k| if k % 2 == 0 { x } else { EDGES[(i + k) % n] });
            let b = core::array::from_fn(|k| {
                if k % 2 == 0 {
                    y
                } else {
                    EDGES[(j + 3 * k) % n]
                }
            });
            if (i * n + j) % EDGE_STRIDE == 0 {
                out.push((a, b));
            }
        }
    }
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for _ in 0..NEAR {
        let a = rng.lanes16();
        // Equal, and equal but for one lane one above or below (in either half of a 64-bit
        // element), so that `<` and `<=` differ on some lanes.
        out.push((a, a));
        let mut b = a;
        let k = (rng.next() % 16) as usize;
        b[k] = if rng.next() & 1 == 0 {
            b[k].wrapping_add(1)
        } else {
            b[k].wrapping_sub(1)
        };
        out.push((a, b));
    }
    for _ in 0..random {
        out.push((rng.lanes16(), rng.lanes16()));
    }
    out
}

/// The cases checked at each immediate or 8-bit mask: `cases(random)`, or under Miri
/// `MIRI_CASES` random pairs.
fn cases_each(random: usize) -> Vec<(L16, L16)> {
    if MIRI {
        let mut rng = Rng(0x1f83_d9ab_fb41_bd6b);
        (0..MIRI_CASES)
            .map(|_| (rng.lanes16(), rng.lanes16()))
            .collect()
    } else {
        cases(random)
    }
}

fn hw512(a: L16) -> hw::__m512i {
    unsafe { transmute(a) }
}

fn hw256(a: L8) -> hw::__m256i {
    unsafe { transmute(a) }
}

fn sh512(a: L16) -> shim::__m512i {
    shim::__m512i(a)
}

fn lanes(v: hw::__m512i) -> L16 {
    unsafe { transmute(v) }
}

fn lanes256(v: hw::__m256i) -> L8 {
    unsafe { transmute(v) }
}

fn low(a: L16) -> L8 {
    a[..8].try_into().unwrap()
}

/// `a` and `b` read as eight 64-bit lanes, as `__m512d` holds them.
fn pd(a: L16) -> [u64; 8] {
    unsafe { transmute(a) }
}

fn agree<T: PartialEq + core::fmt::Debug>(name: &str, inputs: &[&[u32]], hw: T, sh: T) {
    assert_eq!(hw, sh, "{name}: inputs {inputs:08x?}");
}

/// A binary 512-bit shim against its intrinsic, on every case.
macro_rules! binary512 {
    ($test:ident, $f:ident) => {
        #[test]
        fn $test() {
            require_avx512!();
            for (a, b) in cases(RANDOM) {
                let h = lanes(unsafe { hw::$f(hw512(a), hw512(b)) });
                let s = unsafe { shim::$f(sh512(a), sh512(b)) }.0;
                agree(stringify!($f), &[&a, &b], h, s);
            }
        }
    };
}

binary512!(add_epi32, _mm512_add_epi32);
binary512!(sub_epi32, _mm512_sub_epi32);
binary512!(add_epi64, _mm512_add_epi64);
binary512!(sub_epi64, _mm512_sub_epi64);
binary512!(min_epu32, _mm512_min_epu32);
binary512!(mul_epu32, _mm512_mul_epu32);
binary512!(mul_epi32, _mm512_mul_epi32);
binary512!(and_si512, _mm512_and_si512);
binary512!(madd_epi16, _mm512_madd_epi16);
binary512!(maddubs_epi16, _mm512_maddubs_epi16);

/// A comparison into a 16-bit mask against its intrinsic, on every case.
macro_rules! compare512 {
    ($test:ident, $f:ident) => {
        #[test]
        fn $test() {
            require_avx512!();
            for (a, b) in cases(RANDOM) {
                let h: u16 = unsafe { hw::$f(hw512(a), hw512(b)) };
                let s: u16 = unsafe { shim::$f(sh512(a), sh512(b)) };
                agree(stringify!($f), &[&a, &b], h, s);
            }
        }
    };
}

compare512!(cmplt_epu32_mask, _mm512_cmplt_epu32_mask);
compare512!(cmplt_epi32_mask, _mm512_cmplt_epi32_mask);
compare512!(cmple_epu32_mask, _mm512_cmple_epu32_mask);
compare512!(test_epi32_mask, _mm512_test_epi32_mask);

#[test]
fn cmple_epu64_mask() {
    require_avx512!();
    for (a, b) in cases(RANDOM) {
        let h: u8 = unsafe { hw::_mm512_cmple_epu64_mask(hw512(a), hw512(b)) };
        let s: u8 = unsafe { shim::_mm512_cmple_epu64_mask(sh512(a), sh512(b)) };
        agree("_mm512_cmple_epu64_mask", &[&a, &b], h, s);
    }
}

#[test]
fn mm256_cmplt_epu32_mask() {
    require_avx512!();
    for (a, b) in cases(RANDOM) {
        let (a, b) = (low(a), low(b));
        let h: u8 = unsafe { hw::_mm256_cmplt_epu32_mask(hw256(a), hw256(b)) };
        let s: u8 = unsafe { shim::_mm256_cmplt_epu32_mask(shim::__m256i(a), shim::__m256i(b)) };
        agree("_mm256_cmplt_epu32_mask", &[&a, &b], h, s);
    }
}

/// The 16-bit masked shims at mask `k`, on `src`, `a` and `b`.
fn masked16(k: u16, src: L16, a: L16, b: L16) {
    let ins: &[&[u32]] = &[&[k as u32], &src, &a, &b];
    unsafe {
        agree(
            "_mm512_mask_add_epi32",
            ins,
            lanes(hw::_mm512_mask_add_epi32(hw512(src), k, hw512(a), hw512(b))),
            shim::_mm512_mask_add_epi32(sh512(src), k, sh512(a), sh512(b)).0,
        );
        agree(
            "_mm512_mask_sub_epi32",
            ins,
            lanes(hw::_mm512_mask_sub_epi32(hw512(src), k, hw512(a), hw512(b))),
            shim::_mm512_mask_sub_epi32(sh512(src), k, sh512(a), sh512(b)).0,
        );
        agree(
            "_mm512_maskz_sub_epi32",
            ins,
            lanes(hw::_mm512_maskz_sub_epi32(k, hw512(a), hw512(b))),
            shim::_mm512_maskz_sub_epi32(k, sh512(a), sh512(b)).0,
        );
        agree(
            "_mm512_mask_blend_epi32",
            ins,
            lanes(hw::_mm512_mask_blend_epi32(k, hw512(a), hw512(b))),
            shim::_mm512_mask_blend_epi32(k, sh512(a), sh512(b)).0,
        );
        let h: L16 = transmute(hw::_mm512_mask_movehdup_ps(
            transmute::<L16, hw::__m512>(src),
            k,
            transmute::<L16, hw::__m512>(a),
        ));
        let s = shim::_mm512_mask_movehdup_ps(shim::__m512(src), k, shim::__m512(a)).0;
        agree("_mm512_mask_movehdup_ps", ins, h, s);
    }
}

/// The 8-bit masked shims at mask `k`, on `src`, `a` and `b`.
fn masked8(k: u8, src: L16, a: L16, b: L16) {
    let ins: &[&[u32]] = &[&[k as u32], &src, &a, &b];
    unsafe {
        agree(
            "_mm512_mask_sub_epi64",
            ins,
            lanes(hw::_mm512_mask_sub_epi64(hw512(src), k, hw512(a), hw512(b))),
            shim::_mm512_mask_sub_epi64(sh512(src), k, sh512(a), sh512(b)).0,
        );
        agree(
            "_mm512_mask_blend_epi64",
            ins,
            lanes(hw::_mm512_mask_blend_epi64(k, hw512(a), hw512(b))),
            shim::_mm512_mask_blend_epi64(k, sh512(a), sh512(b)).0,
        );
        let (src, a, b) = (low(src), low(a), low(b));
        agree(
            "_mm256_mask_add_epi32",
            ins,
            lanes256(hw::_mm256_mask_add_epi32(hw256(src), k, hw256(a), hw256(b))),
            shim::_mm256_mask_add_epi32(shim::__m256i(src), k, shim::__m256i(a), shim::__m256i(b))
                .0,
        );
        let h: L8 = transmute(hw::_mm256_mask_movehdup_ps(
            transmute::<L8, hw::__m256>(src),
            k,
            transmute::<L8, hw::__m256>(a),
        ));
        let s = shim::_mm256_mask_movehdup_ps(shim::__m256(src), k, shim::__m256(a)).0;
        agree("_mm256_mask_movehdup_ps", ins, h, s);
    }
}

#[test]
fn masked16_random_masks() {
    require_avx512!();
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    for (a, b) in cases(RANDOM) {
        let src = rng.lanes16();
        masked16(rng.mask16(), src, a, b);
    }
}

#[test]
fn masked16_every_mask() {
    require_avx512!();
    let mut rng = Rng(0x6a09_e667_f3bc_c908);
    let vectors: Vec<(L16, L16, L16)> = (0..4)
        .map(|_| (rng.lanes16(), rng.lanes16(), rng.lanes16()))
        .collect();
    for k in (0..=u16::MAX).step_by(MASK16_STRIDE) {
        for &(src, a, b) in &vectors {
            masked16(k, src, a, b);
        }
    }
}

#[test]
fn masked8_every_mask() {
    require_avx512!();
    let mut rng = Rng(0xbb67_ae85_84ca_a73b);
    let cs = cases_each(RANDOM_PER_MASK8);
    for k in 0..=u8::MAX {
        for &(a, b) in &cs {
            masked8(k, rng.lanes16(), a, b);
        }
    }
}

/// Calls `$f::<I>($cases)` for every 8-bit immediate `I`, by halving the range.
macro_rules! each_imm8 {
    ($f:ident, $c:expr) => { each_imm8!(@7 $f, $c, 0) };
    (@7 $f:ident, $c:expr, $b:expr) => { each_imm8!(@6 $f, $c, $b); each_imm8!(@6 $f, $c, $b + 128) };
    (@6 $f:ident, $c:expr, $b:expr) => { each_imm8!(@5 $f, $c, $b); each_imm8!(@5 $f, $c, $b + 64) };
    (@5 $f:ident, $c:expr, $b:expr) => { each_imm8!(@4 $f, $c, $b); each_imm8!(@4 $f, $c, $b + 32) };
    (@4 $f:ident, $c:expr, $b:expr) => { each_imm8!(@3 $f, $c, $b); each_imm8!(@3 $f, $c, $b + 16) };
    (@3 $f:ident, $c:expr, $b:expr) => { each_imm8!(@2 $f, $c, $b); each_imm8!(@2 $f, $c, $b + 8) };
    (@2 $f:ident, $c:expr, $b:expr) => { each_imm8!(@1 $f, $c, $b); each_imm8!(@1 $f, $c, $b + 4) };
    (@1 $f:ident, $c:expr, $b:expr) => { each_imm8!(@0 $f, $c, $b); each_imm8!(@0 $f, $c, $b + 2) };
    (@0 $f:ident, $c:expr, $b:expr) => { $f::<{ $b }>($c); $f::<{ $b + 1 }>($c) };
}

/// The shifts whose immediate `core::arch` types as a `u32`, on every case. The masked shift
/// takes a mask from the case's second input.
fn shifts_u32<const I: u32>(cases: &[(L16, L16)]) {
    for &(a, b) in cases {
        let k = b[0] as u16;
        unsafe {
            agree(
                &format!("_mm512_srli_epi32::<{I}>"),
                &[&a],
                lanes(hw::_mm512_srli_epi32::<I>(hw512(a))),
                shim::_mm512_srli_epi32::<I>(sh512(a)).0,
            );
            agree(
                &format!("_mm512_slli_epi64::<{I}>"),
                &[&a],
                lanes(hw::_mm512_slli_epi64::<I>(hw512(a))),
                shim::_mm512_slli_epi64::<I>(sh512(a)).0,
            );
            agree(
                &format!("_mm512_mask_slli_epi32::<{I}>"),
                &[&[k as u32], &b, &a],
                lanes(hw::_mm512_mask_slli_epi32::<I>(hw512(b), k, hw512(a))),
                shim::_mm512_mask_slli_epi32::<I>(sh512(b), k, sh512(a)).0,
            );
        }
    }
}

/// The shuffles and the double shift, whose immediate `core::arch` types as an `i32`.
fn shuffles_i32<const I: i32>(cases: &[(L16, L16)]) {
    for &(a, b) in cases {
        unsafe {
            agree(
                &format!("_mm512_shuffle_epi32::<{I}>"),
                &[&a],
                lanes(hw::_mm512_shuffle_epi32::<I>(hw512(a))),
                shim::_mm512_shuffle_epi32::<I>(sh512(a)).0,
            );
            agree(
                &format!("_mm512_shuffle_i64x2::<{I}>"),
                &[&a, &b],
                lanes(hw::_mm512_shuffle_i64x2::<I>(hw512(a), hw512(b))),
                shim::_mm512_shuffle_i64x2::<I>(sh512(a), sh512(b)).0,
            );
            let h: [u64; 8] = transmute(hw::_mm512_shuffle_pd::<I>(
                transmute::<L16, hw::__m512d>(a),
                transmute::<L16, hw::__m512d>(b),
            ));
            let s = shim::_mm512_shuffle_pd::<I>(shim::__m512d(pd(a)), shim::__m512d(pd(b))).0;
            agree(&format!("_mm512_shuffle_pd::<{I}>"), &[&a, &b], h, s);
            agree(
                &format!("_mm512_shrdi_epi64::<{I}>"),
                &[&a, &b],
                lanes(hw::_mm512_shrdi_epi64::<I>(hw512(a), hw512(b))),
                shim::_mm512_shrdi_epi64::<I>(sh512(a), sh512(b)).0,
            );
        }
    }
}

#[test]
fn shifts_every_imm8() {
    require_avx512!();
    each_imm8!(shifts_u32, &cases_each(RANDOM_PER_IMM));
}

#[test]
fn shuffles_every_imm8() {
    require_avx512!();
    each_imm8!(shuffles_i32, &cases_each(RANDOM_PER_IMM));
}

#[test]
#[cfg_attr(miri, ignore = "Miri does not implement `vpermi2d` and `vpermi2q`")]
fn permutex2var() {
    require_avx512!();
    let mut rng = Rng(0x3c6e_f372_fe94_f82b);
    for (a, b) in cases(RANDOM) {
        // Every lane of the index is random: the bits above those the instruction reads must
        // be ignored too.
        let idx: L16 = core::array::from_fn(|_| rng.next() as u32);
        unsafe {
            agree(
                "_mm512_permutex2var_epi32",
                &[&a, &idx, &b],
                lanes(hw::_mm512_permutex2var_epi32(
                    hw512(a),
                    hw512(idx),
                    hw512(b),
                )),
                shim::_mm512_permutex2var_epi32(sh512(a), sh512(idx), sh512(b)).0,
            );
            agree(
                "_mm512_permutex2var_epi64",
                &[&a, &idx, &b],
                lanes(hw::_mm512_permutex2var_epi64(
                    hw512(a),
                    hw512(idx),
                    hw512(b),
                )),
                shim::_mm512_permutex2var_epi64(sh512(a), sh512(idx), sh512(b)).0,
            );
        }
    }
}

#[test]
fn movehdup_and_casts() {
    require_avx512!();
    for (a, _) in cases(RANDOM) {
        unsafe {
            let h: L16 = transmute(hw::_mm512_movehdup_ps(hw::_mm512_castsi512_ps(hw512(a))));
            let s = shim::_mm512_movehdup_ps(shim::_mm512_castsi512_ps(sh512(a))).0;
            agree("_mm512_movehdup_ps", &[&a], h, s);
            let h: L16 = transmute(hw::_mm512_castsi512_ps(hw512(a)));
            agree(
                "_mm512_castsi512_ps",
                &[&a],
                h,
                shim::_mm512_castsi512_ps(sh512(a)).0,
            );
            let back = hw::_mm512_castps_si512(transmute::<L16, hw::__m512>(a));
            let s = shim::_mm512_castps_si512(shim::__m512(a)).0;
            agree("_mm512_castps_si512", &[&a], lanes(back), s);
            let h: [u64; 8] = transmute(hw::_mm512_castsi512_pd(hw512(a)));
            agree(
                "_mm512_castsi512_pd",
                &[&a],
                h,
                shim::_mm512_castsi512_pd(sh512(a)).0,
            );
            let back = hw::_mm512_castpd_si512(transmute::<L16, hw::__m512d>(a));
            let s = shim::_mm512_castpd_si512(shim::__m512d(pd(a))).0;
            agree("_mm512_castpd_si512", &[&a], lanes(back), s);
            agree(
                "_mm512_castsi512_si256",
                &[&a],
                lanes256(hw::_mm512_castsi512_si256(hw512(a))),
                shim::_mm512_castsi512_si256(sh512(a)).0,
            );
        }
    }
}

#[test]
fn constructors() {
    require_avx512!();
    let mut rng = Rng(0x510e_527f_ade6_82d1);
    let zero = unsafe { (hw::_mm512_setzero_epi32(), shim::_mm512_setzero_epi32()) };
    agree("_mm512_setzero_epi32", &[], lanes(zero.0), zero.1.0);
    let xs: Vec<u32> = EDGES
        .iter()
        .copied()
        .chain((0..RANDOM).map(|_| rng.lane()))
        .collect();
    for x in xs {
        let x = x as i32;
        let h = unsafe { hw::_mm512_set1_epi32(x) };
        agree(
            "_mm512_set1_epi32",
            &[&[x as u32]],
            lanes(h),
            unsafe { shim::_mm512_set1_epi32(x) }.0,
        );
    }
}

/// The shim types have the size of the registers they stand for.
#[test]
fn layouts() {
    use core::mem::size_of;
    assert_eq!(size_of::<shim::__m512i>(), size_of::<hw::__m512i>());
    assert_eq!(size_of::<shim::__m512>(), size_of::<hw::__m512>());
    assert_eq!(size_of::<shim::__m512d>(), size_of::<hw::__m512d>());
    assert_eq!(size_of::<shim::__mmask16>(), size_of::<hw::__mmask16>());
    assert_eq!(size_of::<shim::__mmask8>(), size_of::<hw::__mmask8>());
}
