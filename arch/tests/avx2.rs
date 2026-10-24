//! Differential tests: every shim against the `core::arch` intrinsic it models.
//!
//! The inputs are lanes drawn from edge values (zero, one, sign and carry boundaries, the
//! 31-bit primes) and from a fixed-seed generator, and every shim that takes an immediate is
//! checked at all 256 values of its 8-bit immediate. The tests need an x86_64 build with AVX2:
//!
//!     RUSTFLAGS="-C target-feature=+avx2" cargo test --target <x86_64 triple>
//!
//! Elsewhere the file compiles to nothing.
#![cfg(all(target_arch = "x86_64", target_feature = "avx2"))]

use core::arch::x86_64 as hw;
use core::mem::transmute;

use p3_arch_shims::x86_64 as shim;

const EDGES: [u32; 22] = [
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
    0x7800_0001, // BabyBear
    0x7f00_0001, // KoalaBear
    0x7fff_fffe,
    0x7fff_ffff,
    0x8000_0000,
    0x8000_0001,
    0xf000_0000,
    0xfffe_ffff,
    0xffff_0000,
    0xffff_fffe,
    0xffff_ffff,
];

const RANDOM: usize = 100_000;
/// Random cases per immediate, for the shims checked at all 256 immediates.
const RANDOM_PER_IMM: usize = 2_000;

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

    fn lanes8(&mut self) -> [u32; 8] {
        core::array::from_fn(|_| self.lane())
    }
}

/// Pairs of 8-lane inputs: each pair of edge values, in the even lanes, with edge values
/// rotating through the odd lanes; then `random` mixed vectors.
fn cases(random: usize) -> Vec<([u32; 8], [u32; 8])> {
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
            out.push((a, b));
        }
    }
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for _ in 0..random {
        out.push((rng.lanes8(), rng.lanes8()));
    }
    out
}

fn hw256(a: [u32; 8]) -> hw::__m256i {
    unsafe { transmute(a) }
}

fn hw128(a: [u32; 4]) -> hw::__m128i {
    unsafe { transmute(a) }
}

fn sh256(a: [u32; 8]) -> shim::__m256i {
    shim::__m256i(a)
}

fn lanes(v: hw::__m256i) -> [u32; 8] {
    unsafe { transmute(v) }
}

fn agree(name: &str, a: &[u32], b: &[u32], hw: &[u32], sh: &[u32]) {
    assert_eq!(hw, sh, "{name}: a = {a:08x?}, b = {b:08x?}");
}

/// A binary 256-bit shim against its intrinsic, on every case.
macro_rules! binary256 {
    ($test:ident, $f:ident) => {
        #[test]
        fn $test() {
            for (a, b) in cases(RANDOM) {
                let h = lanes(unsafe { hw::$f(hw256(a), hw256(b)) });
                let s = unsafe { shim::$f(sh256(a), sh256(b)) }.0;
                agree(stringify!($f), &a, &b, &h, &s);
            }
        }
    };
}

binary256!(add_epi32, _mm256_add_epi32);
binary256!(sub_epi32, _mm256_sub_epi32);
binary256!(add_epi64, _mm256_add_epi64);
binary256!(sub_epi64, _mm256_sub_epi64);
binary256!(min_epu32, _mm256_min_epu32);
binary256!(mul_epu32, _mm256_mul_epu32);
binary256!(mul_epi32, _mm256_mul_epi32);
binary256!(and_si256, _mm256_and_si256);
binary256!(madd_epi16, _mm256_madd_epi16);
binary256!(maddubs_epi16, _mm256_maddubs_epi16);
binary256!(sign_epi32, _mm256_sign_epi32);
binary256!(unpacklo_epi64, _mm256_unpacklo_epi64);
binary256!(unpackhi_epi64, _mm256_unpackhi_epi64);

/// A binary 128-bit shim against its intrinsic, on the low halves of every case.
macro_rules! binary128 {
    ($test:ident, $f:ident) => {
        #[test]
        fn $test() {
            for (a, b) in cases(RANDOM) {
                let a: [u32; 4] = a[..4].try_into().unwrap();
                let b: [u32; 4] = b[..4].try_into().unwrap();
                let h: [u32; 4] = unsafe { transmute(hw::$f(hw128(a), hw128(b))) };
                let s = unsafe { shim::$f(shim::__m128i(a), shim::__m128i(b)) }.0;
                agree(stringify!($f), &a, &b, &h, &s);
            }
        }
    };
}

binary128!(mm_add_epi32, _mm_add_epi32);
binary128!(mm_sub_epi32, _mm_sub_epi32);
binary128!(mm_min_epu32, _mm_min_epu32);

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

fn blend_epi32<const I: i32>(cases: &[([u32; 8], [u32; 8])]) {
    for &(a, b) in cases {
        let h = lanes(unsafe { hw::_mm256_blend_epi32::<I>(hw256(a), hw256(b)) });
        let s = unsafe { shim::_mm256_blend_epi32::<I>(sh256(a), sh256(b)) }.0;
        agree(&format!("_mm256_blend_epi32::<{I}>"), &a, &b, &h, &s);
    }
}

fn permute2x128<const I: i32>(cases: &[([u32; 8], [u32; 8])]) {
    for &(a, b) in cases {
        let h = lanes(unsafe { hw::_mm256_permute2x128_si256::<I>(hw256(a), hw256(b)) });
        let s = unsafe { shim::_mm256_permute2x128_si256::<I>(sh256(a), sh256(b)) }.0;
        agree(&format!("_mm256_permute2x128_si256::<{I}>"), &a, &b, &h, &s);
    }
}

/// The four shifts by an immediate, each on the first input of every case.
fn shifts<const I: i32>(cases: &[([u32; 8], [u32; 8])]) {
    for &(a, _) in cases {
        let checks = unsafe {
            [
                (
                    "_mm256_slli_epi32",
                    hw::_mm256_slli_epi32::<I>(hw256(a)),
                    shim::_mm256_slli_epi32::<I>(sh256(a)),
                ),
                (
                    "_mm256_srli_epi32",
                    hw::_mm256_srli_epi32::<I>(hw256(a)),
                    shim::_mm256_srli_epi32::<I>(sh256(a)),
                ),
                (
                    "_mm256_slli_epi64",
                    hw::_mm256_slli_epi64::<I>(hw256(a)),
                    shim::_mm256_slli_epi64::<I>(sh256(a)),
                ),
                (
                    "_mm256_srli_epi64",
                    hw::_mm256_srli_epi64::<I>(hw256(a)),
                    shim::_mm256_srli_epi64::<I>(sh256(a)),
                ),
            ]
        };
        for (name, h, s) in checks {
            agree(&format!("{name}::<{I}>"), &a, &[], &lanes(h), &s.0);
        }
    }
}

#[test]
fn blend_epi32_every_imm8() {
    each_imm8!(blend_epi32, &cases(RANDOM_PER_IMM));
}

#[test]
fn permute2x128_si256_every_imm8() {
    each_imm8!(permute2x128, &cases(RANDOM_PER_IMM));
}

#[test]
fn shifts_every_imm8() {
    each_imm8!(shifts, &cases(RANDOM_PER_IMM));
}

#[test]
fn movehdup_and_casts() {
    for (a, _) in cases(RANDOM) {
        let h: [u32; 8] =
            unsafe { transmute(hw::_mm256_movehdup_ps(hw::_mm256_castsi256_ps(hw256(a)))) };
        let s = unsafe { shim::_mm256_movehdup_ps(shim::_mm256_castsi256_ps(sh256(a))) }.0;
        agree("_mm256_movehdup_ps", &a, &[], &h, &s);
        let h: [u32; 8] = unsafe { transmute(hw::_mm256_castsi256_ps(hw256(a))) };
        agree(
            "_mm256_castsi256_ps",
            &a,
            &[],
            &h,
            &unsafe { shim::_mm256_castsi256_ps(sh256(a)) }.0,
        );
        let back = unsafe { hw::_mm256_castps_si256(transmute::<[u32; 8], hw::__m256>(a)) };
        let s = unsafe { shim::_mm256_castps_si256(shim::__m256(a)) }.0;
        agree("_mm256_castps_si256", &a, &[], &lanes(back), &s);
    }
}

#[test]
fn constructors() {
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let zero = unsafe { (hw::_mm256_setzero_si256(), shim::_mm256_setzero_si256()) };
    agree("_mm256_setzero_si256", &[], &[], &lanes(zero.0), &zero.1.0);
    let xs: Vec<u32> = EDGES
        .iter()
        .copied()
        .chain((0..RANDOM).map(|_| rng.lane()))
        .collect();
    for x in xs {
        let x = x as i32;
        let e = rng.lanes8().map(|l| l as i32);
        let h = unsafe { hw::_mm256_set1_epi32(x) };
        agree(
            "_mm256_set1_epi32",
            &[x as u32],
            &[],
            &lanes(h),
            &unsafe { shim::_mm256_set1_epi32(x) }.0,
        );
        let h: [u32; 4] = unsafe { transmute(hw::_mm_set1_epi32(x)) };
        agree(
            "_mm_set1_epi32",
            &[x as u32],
            &[],
            &h,
            &unsafe { shim::_mm_set1_epi32(x) }.0,
        );
        let h = unsafe { hw::_mm256_setr_epi32(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7]) };
        let s = unsafe { shim::_mm256_setr_epi32(e[0], e[1], e[2], e[3], e[4], e[5], e[6], e[7]) };
        agree(
            "_mm256_setr_epi32",
            &e.map(|l| l as u32),
            &[],
            &lanes(h),
            &s.0,
        );
    }
}

/// The shim types have the size of the registers they stand for.
#[test]
fn layouts() {
    use core::mem::size_of;
    assert_eq!(size_of::<shim::__m256i>(), size_of::<hw::__m256i>());
    assert_eq!(size_of::<shim::__m128i>(), size_of::<hw::__m128i>());
    assert_eq!(size_of::<shim::__m256>(), size_of::<hw::__m256>());
}
