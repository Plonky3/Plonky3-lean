//! Differential tests: every NEON shim against the `core::arch::aarch64` intrinsic it models.
//!
//! The inputs are lanes drawn from edge values (zero, one, sign and carry boundaries, the
//! 31-bit primes and their neighbours) and from a fixed-seed generator. Small inputs are checked
//! exhaustively: every pair of lanes from the lowest and highest 256 values of a lane, and every
//! shift amount the intrinsic accepts. `vqdmulhq_s32`, whose saturation and rounding are the
//! subtle part, is also checked on every 16-bit signed value against every edge value. The tests
//! need an AArch64 build (NEON is part of the base target):
//!
//!     cargo test --release --test neon
//!
//! Elsewhere the file compiles to nothing.
#![cfg(all(target_arch = "aarch64", target_feature = "neon"))]

use core::arch::aarch64 as hw;
use core::mem::transmute;

use p3_arch_shims::aarch64 as shim;

const EDGES: [u32; 30] = [
    0,
    1,
    2,
    3,
    0x7f,
    0x80,
    0xff,
    0x7fff,
    0x8000,
    0xffff,
    0x1_0000,
    0x7800_0000, // BabyBear P - 1
    0x7800_0001, // BabyBear P
    0x7800_0002, // BabyBear P + 1
    0x7f00_0000, // KoalaBear P - 1
    0x7f00_0001, // KoalaBear P
    0x7fff_fffe,
    0x7fff_ffff, // 2^31 - 1, i32::MAX
    0x8000_0000, // 2^31, i32::MIN
    0x8000_0001,
    0x87ff_ffff, // -BabyBear P
    0x8800_0001, // BabyBear MU, and -(P - 2^32)
    0x80ff_ffff, // -KoalaBear P
    0xf000_0000,
    0xfffe_ffff,
    0xffff_0000,
    0xffff_fffe,
    0xffff_ffff, // u32::MAX, -1
    0x5555_5555,
    0xaaaa_aaaa,
];

const RANDOM: usize = 200_000;
/// Random cases per shift amount, for the shims checked at every shift.
const RANDOM_PER_SHIFT: usize = 5_000;

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

    fn lanes4(&mut self) -> [u32; 4] {
        core::array::from_fn(|_| self.lane())
    }

    /// A 64-bit lane: two 32-bit lanes.
    fn lane64(&mut self) -> u64 {
        (self.lane() as u64) | ((self.lane() as u64) << 32)
    }
}

/// Pairs of 4-lane inputs: every pair of edge values, in lanes 0 and 2, with edge values
/// rotating through lanes 1 and 3; then `random` mixed vectors.
fn cases(random: usize) -> Vec<([u32; 4], [u32; 4])> {
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
        out.push((rng.lanes4(), rng.lanes4()));
    }
    out
}

/// Every pair `(x, y)` of the lowest and highest 256 lane values, four pairs per case.
fn small_cases() -> Vec<([u32; 4], [u32; 4])> {
    let vals: Vec<u32> = (0..256u32)
        .chain((0..256u32).map(|k| u32::MAX - k))
        .collect();
    let pairs: Vec<(u32, u32)> = vals
        .iter()
        .flat_map(|&x| vals.iter().map(move |&y| (x, y)))
        .collect();
    pairs
        .chunks(4)
        .map(|c| {
            (
                core::array::from_fn(|k| c[k].0),
                core::array::from_fn(|k| c[k].1),
            )
        })
        .collect()
}

/// Every case the binary shims are checked on.
fn all_cases() -> Vec<([u32; 4], [u32; 4])> {
    let mut out = cases(RANDOM);
    out.extend(small_cases());
    out
}

fn hu(a: [u32; 4]) -> hw::uint32x4_t {
    unsafe { transmute(a) }
}

fn hs(a: [u32; 4]) -> hw::int32x4_t {
    unsafe { transmute(a) }
}

fn hu64(a: [u64; 2]) -> hw::uint64x2_t {
    unsafe { transmute(a) }
}

fn hu2(a: [u32; 2]) -> hw::uint32x2_t {
    unsafe { transmute(a) }
}

fn su(a: [u32; 4]) -> shim::uint32x4_t {
    shim::uint32x4_t(a)
}

fn ss(a: [u32; 4]) -> shim::int32x4_t {
    shim::int32x4_t(a.map(|l| l as i32))
}

/// The lanes of a 128-bit hardware vector, as `u32`s.
fn lanes<T>(v: T) -> [u32; 4] {
    assert_eq!(size_of::<T>(), 16);
    unsafe { core::mem::transmute_copy(&v) }
}

fn lanes64<T>(v: T) -> [u64; 2] {
    assert_eq!(size_of::<T>(), 16);
    unsafe { core::mem::transmute_copy(&v) }
}

fn agree<T: PartialEq + core::fmt::Debug>(name: &str, a: &[u32], b: &[u32], hw: T, sh: T) {
    assert_eq!(hw, sh, "{name}: a = {a:08x?}, b = {b:08x?}");
}

/// A binary shim on unsigned (`u`) or signed (`s`) lanes against its intrinsic, on every case.
macro_rules! binary {
    ($test:ident, $f:ident, $hin:ident, $sin:ident, $out:expr) => {
        #[test]
        fn $test() {
            for (a, b) in all_cases() {
                let h = lanes(unsafe { hw::$f($hin(a), $hin(b)) });
                let s = unsafe { shim::$f($sin(a), $sin(b)) };
                agree(stringify!($f), &a, &b, h, $out(s.0));
            }
        }
    };
}

fn id(x: [u32; 4]) -> [u32; 4] {
    x
}

fn bits(x: [i32; 4]) -> [u32; 4] {
    x.map(|l| l as u32)
}

binary!(vaddq_u32, vaddq_u32, hu, su, id);
binary!(vsubq_u32, vsubq_u32, hu, su, id);
binary!(vandq_u32, vandq_u32, hu, su, id);
binary!(vbicq_u32, vbicq_u32, hu, su, id);
binary!(vminq_u32, vminq_u32, hu, su, id);
binary!(vtstq_u32, vtstq_u32, hu, su, id);
binary!(vcltq_u32, vcltq_u32, hu, su, id);
binary!(vcgeq_u32, vcgeq_u32, hu, su, id);
binary!(vhaddq_u32, vhaddq_u32, hu, su, id);
binary!(vmulq_u32, vmulq_u32, hu, su, id);
binary!(vuzp1q_u32, vuzp1q_u32, hu, su, id);
binary!(vuzp2q_u32, vuzp2q_u32, hu, su, id);
binary!(vtrn1q_u32, vtrn1q_u32, hu, su, id);
binary!(vtrn2q_u32, vtrn2q_u32, hu, su, id);
binary!(vaddq_s32, vaddq_s32, hs, ss, bits);
binary!(vmulq_s32, vmulq_s32, hs, ss, bits);
binary!(vhsubq_s32, vhsubq_s32, hs, ss, bits);
binary!(vqdmulhq_s32, vqdmulhq_s32, hs, ss, bits);
binary!(vcltq_s32, vcltq_s32, hs, ss, id);

/// `vqdmulhq_s32` on every 16-bit signed value against every edge value, in both orders.
/// This covers each sign of each operand, the saturating case `i32::MIN * i32::MIN`, and every
/// product within a factor of `2^16` of an edge.
#[test]
fn vqdmulhq_s32_sweep() {
    for x in i16::MIN..=i16::MAX {
        for &y in &EDGES {
            for (a, b) in [
                (
                    [
                        x as u32,
                        (x as u32) << 15,
                        (x as u32) << 16,
                        (x as i32).wrapping_mul(0x8001) as u32,
                    ],
                    [y; 4],
                ),
                (
                    [y; 4],
                    [
                        x as u32,
                        (x as u32) << 15,
                        (x as u32) << 16,
                        (x as i32).wrapping_mul(0x8001) as u32,
                    ],
                ),
            ] {
                let h = lanes(unsafe { hw::vqdmulhq_s32(hs(a), hs(b)) });
                let s = unsafe { shim::vqdmulhq_s32(ss(a), ss(b)) };
                agree("vqdmulhq_s32", &a, &b, h, bits(s.0));
            }
        }
    }
}

/// `vmlsq_u32` against its intrinsic: the accumulator from one case, the factors from another.
#[test]
fn vmlsq_u32() {
    let cs = all_cases();
    let mut rng = Rng(0x1234_5678_9abc_def1);
    for (i, &(a, b)) in cs.iter().enumerate() {
        let c = if i % 2 == 0 {
            cs[(i * 7 + 1) % cs.len()].0
        } else {
            rng.lanes4()
        };
        let h = lanes(unsafe { hw::vmlsq_u32(hu(a), hu(b), hu(c)) });
        let s = unsafe { shim::vmlsq_u32(su(a), su(b), su(c)) };
        agree("vmlsq_u32", &a, &b, h, s.0);
        let h = lanes(unsafe { hw::vmlsq_n_u32(hu(a), hu(b), c[0]) });
        let s = unsafe { shim::vmlsq_n_u32(su(a), su(b), c[0]) };
        agree("vmlsq_n_u32", &a, &b, h, s.0);
    }
}

/// The unary shims, and the constructors, on every lane of every case.
#[test]
fn unary() {
    for (a, b) in all_cases() {
        agree(
            "vceqzq_u32",
            &a,
            &[],
            lanes(unsafe { hw::vceqzq_u32(hu(a)) }),
            unsafe { shim::vceqzq_u32(su(a)) }.0,
        );
        agree(
            "vreinterpretq_s32_u32",
            &a,
            &[],
            lanes(unsafe { hw::vreinterpretq_s32_u32(hu(a)) }),
            bits(unsafe { shim::vreinterpretq_s32_u32(su(a)) }.0),
        );
        agree(
            "vreinterpretq_u32_s32",
            &a,
            &[],
            lanes(unsafe { hw::vreinterpretq_u32_s32(hs(a)) }),
            unsafe { shim::vreinterpretq_u32_s32(ss(a)) }.0,
        );
        agree(
            "vreinterpretq_u64_u32",
            &a,
            &[],
            lanes64(unsafe { hw::vreinterpretq_u64_u32(hu(a)) }),
            unsafe { shim::vreinterpretq_u64_u32(su(a)) }.0,
        );
        let a64 = [
            (a[0] as u64) | ((b[1] as u64) << 32),
            (b[2] as u64) | ((a[3] as u64) << 32),
        ];
        agree(
            "vreinterpretq_u32_u64",
            &a,
            &b,
            lanes(unsafe { hw::vreinterpretq_u32_u64(hu64(a64)) }),
            unsafe { shim::vreinterpretq_u32_u64(shim::uint64x2_t(a64)) }.0,
        );
        let h: [u32; 2] = unsafe { transmute(hw::vget_low_u32(hu(a))) };
        agree(
            "vget_low_u32",
            &a,
            &[],
            h,
            unsafe { shim::vget_low_u32(su(a)) }.0,
        );
        agree(
            "vdupq_n_u32",
            &a,
            &[],
            lanes(unsafe { hw::vdupq_n_u32(a[1]) }),
            unsafe { shim::vdupq_n_u32(a[1]) }.0,
        );
        agree(
            "vdupq_n_s32",
            &a,
            &[],
            lanes(unsafe { hw::vdupq_n_s32(a[2] as i32) }),
            bits(unsafe { shim::vdupq_n_s32(a[2] as i32) }.0),
        );
    }
}

/// The widening multiplies and the 64-bit transposes. The accumulators are 64-bit lanes from
/// the generator, and their high halves from edge values.
#[test]
fn widening_and_u64() {
    let mut rng = Rng(0x0000_ddb1_a5e5_bad5);
    for (i, (a, b)) in all_cases().into_iter().enumerate() {
        let acc = if i % 3 == 0 {
            [
                (a[3] as u64) << 32 | b[3] as u64,
                (b[0] as u64) << 32 | a[0] as u64,
            ]
        } else {
            [rng.lane64(), rng.lane64()]
        };
        let (lo_a, lo_b) = ([a[0], a[1]], [b[0], b[1]]);
        let checks: [(&str, [u64; 2], [u64; 2]); 6] = unsafe {
            [
                (
                    "vmull_u32",
                    lanes64(hw::vmull_u32(hu2(lo_a), hu2(lo_b))),
                    shim::vmull_u32(shim::uint32x2_t(lo_a), shim::uint32x2_t(lo_b)).0,
                ),
                (
                    "vmull_high_u32",
                    lanes64(hw::vmull_high_u32(hu(a), hu(b))),
                    shim::vmull_high_u32(su(a), su(b)).0,
                ),
                (
                    "vmlal_u32",
                    lanes64(hw::vmlal_u32(hu64(acc), hu2(lo_a), hu2(lo_b))),
                    shim::vmlal_u32(
                        shim::uint64x2_t(acc),
                        shim::uint32x2_t(lo_a),
                        shim::uint32x2_t(lo_b),
                    )
                    .0,
                ),
                (
                    "vmlal_high_u32",
                    lanes64(hw::vmlal_high_u32(hu64(acc), hu(a), hu(b))),
                    shim::vmlal_high_u32(shim::uint64x2_t(acc), su(a), su(b)).0,
                ),
                (
                    "vmlsl_u32",
                    lanes64(hw::vmlsl_u32(hu64(acc), hu2(lo_a), hu2(lo_b))),
                    shim::vmlsl_u32(
                        shim::uint64x2_t(acc),
                        shim::uint32x2_t(lo_a),
                        shim::uint32x2_t(lo_b),
                    )
                    .0,
                ),
                (
                    "vmlsl_high_u32",
                    lanes64(hw::vmlsl_high_u32(hu64(acc), hu(a), hu(b))),
                    shim::vmlsl_high_u32(shim::uint64x2_t(acc), su(a), su(b)).0,
                ),
            ]
        };
        for (name, h, s) in checks {
            agree(name, &a, &b, h, s);
        }
        let (x, y) = ([acc[0], rng.lane64()], [acc[1], rng.lane64()]);
        agree(
            "vtrn1q_u64",
            &a,
            &b,
            lanes64(unsafe { hw::vtrn1q_u64(hu64(x), hu64(y)) }),
            unsafe { shim::vtrn1q_u64(shim::uint64x2_t(x), shim::uint64x2_t(y)) }.0,
        );
        agree(
            "vtrn2q_u64",
            &a,
            &b,
            lanes64(unsafe { hw::vtrn2q_u64(hu64(x), hu64(y)) }),
            unsafe { shim::vtrn2q_u64(shim::uint64x2_t(x), shim::uint64x2_t(y)) }.0,
        );
    }
}

/// Calls `$f::<N>($cases)` for each listed shift amount `N`.
macro_rules! each_shift {
    ($f:ident, $c:expr, [$($n:literal),*]) => { $( $f::<$n>($c); )* };
}

/// `vshrq_n_u32` and `vsraq_n_u32` at `N`, which they accept for `1 <= N <= 32`.
fn shifts_right<const N: i32>(cases: &[([u32; 4], [u32; 4])]) {
    for &(a, b) in cases {
        let h = lanes(unsafe { hw::vshrq_n_u32::<N>(hu(a)) });
        let s = unsafe { shim::vshrq_n_u32::<N>(su(a)) }.0;
        agree(&format!("vshrq_n_u32::<{N}>"), &a, &[], h, s);
        let h = lanes(unsafe { hw::vsraq_n_u32::<N>(hu(a), hu(b)) });
        let s = unsafe { shim::vsraq_n_u32::<N>(su(a), su(b)) }.0;
        agree(&format!("vsraq_n_u32::<{N}>"), &a, &b, h, s);
    }
}

/// `vshlq_n_u32` at `N`, which it accepts for `0 <= N <= 31`.
fn shifts_left<const N: i32>(cases: &[([u32; 4], [u32; 4])]) {
    for &(a, _) in cases {
        let h = lanes(unsafe { hw::vshlq_n_u32::<N>(hu(a)) });
        let s = unsafe { shim::vshlq_n_u32::<N>(su(a)) }.0;
        agree(&format!("vshlq_n_u32::<{N}>"), &a, &[], h, s);
    }
}

#[test]
fn shifts_right_every_n() {
    let cs = cases(RANDOM_PER_SHIFT);
    each_shift!(
        shifts_right,
        &cs,
        [
            1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24,
            25, 26, 27, 28, 29, 30, 31, 32
        ]
    );
}

#[test]
fn shifts_left_every_n() {
    let cs = cases(RANDOM_PER_SHIFT);
    each_shift!(
        shifts_left,
        &cs,
        [
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
            24, 25, 26, 27, 28, 29, 30, 31
        ]
    );
}

/// The shim types have the size of the registers they stand for.
#[test]
fn layouts() {
    assert_eq!(size_of::<shim::uint32x4_t>(), size_of::<hw::uint32x4_t>());
    assert_eq!(size_of::<shim::int32x4_t>(), size_of::<hw::int32x4_t>());
    assert_eq!(size_of::<shim::uint64x2_t>(), size_of::<hw::uint64x2_t>());
    assert_eq!(size_of::<shim::uint32x2_t>(), size_of::<hw::uint32x2_t>());
}
