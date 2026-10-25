#!/usr/bin/env bash
#
# check-mutations.sh -- show that the differential tests can fail.
#
# mutations/<shim>.patch is a recorded mutation of one shim: a plausible bug
# (`# Breaks:` says which). For each one, on a scratch copy of this crate, the
# tests must pass as written, then fail with the mutation applied. A shim whose
# mutation every test survives is not covered, and the run fails.
#
# The tests compare against the hardware, so each suite runs where its
# intrinsics do, and checks the mutations of its own shims:
#
#   - AVX2 (tests/avx2.rs, the mutations of src/x86_64/avx2.rs): an x86_64
#     build with AVX2, selected by RUSTFLAGS, e.g. `--target x86_64-apple-darwin`
#     under Rosetta:
#       RUSTFLAGS="-C target-feature=+avx2" arch/check-mutations.sh [cargo test args...]
#   - AVX-512 (tests/avx512.rs, the mutations of src/x86_64/avx512.rs): an
#     x86_64 build with the AVX-512 features the backend names:
#       RUSTFLAGS="-C target-feature=+avx512f,+avx512bw,+avx512vl,+avx512vbmi2" \
#         arch/check-mutations.sh [cargo test args...]
#     On a CPU without them (checked in /proc/cpuinfo, or by sysctl on macOS)
#     the tests cannot run. The script then says so, and checks less:
#       - with MIRI_TOOLCHAIN set to a toolchain with Miri (e.g. `nightly`),
#         it runs the suite under Miri, where each intrinsic is core::arch's own
#         Rust implementation, not the hardware. Pass the x86_64 target among
#         the cargo arguments, e.g. `--target x86_64-unknown-linux-gnu`. A
#         mutation whose `# Miri:` line says Miri cannot run its tests is only
#         compiled;
#       - otherwise it only shows that each mutation applies and compiles.
#   - NEON (tests/neon.rs, the mutations of src/aarch64/): an AArch64 host,
#     with RUSTFLAGS naming neither AVX2 nor AVX-512:
#       arch/check-mutations.sh [cargo test args...]
set -eu

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
case "${RUSTFLAGS:-}" in
    *avx512*) SUITE=avx512; SRC=src/x86_64/avx512.rs ;;
    *avx2*) SUITE=avx2; SRC=src/x86_64/avx2.rs ;;
    *)
        case "$(rustc -vV | sed -n 's/^host: //p')" in
            aarch64-*) SUITE=neon; SRC=src/aarch64/ ;;
            *) echo "error: on x86_64, set RUSTFLAGS to enable AVX2 or AVX-512 (see the header)" >&2; exit 2 ;;
        esac ;;
esac

# Whether this CPU has the features tests/avx512.rs is compiled for.
has_avx512() {
    if [ -r /proc/cpuinfo ]; then
        local flags f
        flags="$(grep -m1 '^flags' /proc/cpuinfo || true)"
        for f in avx512f avx512bw avx512vl avx512_vbmi2; do
            printf '%s\n' "$flags" | grep -qw "$f" || return 1
        done
        return 0
    fi
    local leaf7
    leaf7="$(sysctl -n machdep.cpu.leaf7_features 2>/dev/null || true)"
    for f in AVX512F AVX512BW AVX512VL VBMI2; do
        printf '%s\n' "$leaf7" | grep -qw "$f" || return 1
    done
}

# hardware: run the tests natively. miri: run them under Miri. compile: only build them.
MODE=hardware
if [ "$SUITE" = avx512 ] && ! has_avx512; then
    if [ -n "${MIRI_TOOLCHAIN:-}" ]; then
        MODE=miri
        echo "skipped: no AVX-512 on this CPU; running the AVX-512 suite under Miri ($MIRI_TOOLCHAIN)"
        echo "         instead, against core::arch's own implementation of each intrinsic"
    else
        MODE=compile
        echo "skipped: no AVX-512 on this CPU; checking only that each AVX-512 mutation"
        echo "         applies and compiles (set MIRI_TOOLCHAIN to run the tests under Miri)"
    fi
fi
echo "suite: tests/$SUITE.rs, the mutations of $SRC ($MODE)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$TMP/target}"
rsync -a --exclude target/ --exclude mutations/ "$HERE/" "$TMP/crate/"

run() {   # the differential tests; prints the number that passed and failed
    case "$MODE" in
        miri) (cd "$TMP/crate" && MIRIFLAGS="${MIRIFLAGS:--Zmiri-disable-stacked-borrows -Zmiri-disable-validation}" \
                cargo "+$MIRI_TOOLCHAIN" miri test --quiet --test "$SUITE" "$@" 2>&1) ;;
        *) (cd "$TMP/crate" && cargo test --quiet --locked --release --test "$SUITE" "$@" 2>&1) ;;
    esac | sed -n 's/^test result: [A-Za-z]*\. \([0-9]*\) passed; \([0-9]*\) failed.*/\1 \2/p' | tail -1
}

builds() {   # the crate and the differential tests type-check (nothing is linked or run)
    (cd "$TMP/crate" && cargo check --quiet --locked --release --tests "$@") >/dev/null 2>&1
}

if [ "$MODE" = compile ]; then
    # tests/avx512.rs compiles to nothing unless RUSTFLAGS enables every feature it needs.
    for f in avx512f avx512bw avx512vl avx512vbmi2; do
        case "$RUSTFLAGS" in
            *"+$f"*) ;;
            *) echo "error: RUSTFLAGS must enable $f, or tests/$SUITE.rs is not compiled (see the header)" >&2
               exit 1 ;;
        esac
    done
    builds "$@" || { echo "error: the tests do not compile as written" >&2; exit 1; }
    echo "as written: the tests compile"
else
    read -r passed failed <<< "$(run "$@")"
    if [ "${passed:-0}" -eq 0 ] || [ "${failed:-1}" -ne 0 ]; then
        echo "error: the tests do not pass as written (${passed:-0} passed, ${failed:-?} failed)" >&2
        exit 1
    fi
    echo "as written: $passed test(s) pass"
fi

fail=0
n=0
compiled=0
for m in "$HERE"/mutations/*.patch; do
    grep -q "^+++ b/$SRC" "$m" || continue
    n=$((n + 1))
    name="$(basename "$m" .patch)"
    breaks="$(sed -n 's/^# Breaks:[[:space:]]*//p' "$m")"
    nomiri="$(sed -n 's/^# Miri:[[:space:]]*//p' "$m")"
    patch -s -p1 -F0 --no-backup-if-mismatch -d "$TMP/crate" < "$m"
    if [ "$MODE" = compile ] || { [ "$MODE" = miri ] && [ -n "$nomiri" ]; }; then
        if builds "$@"; then
            why="no AVX-512"; [ "$MODE" = compile ] || why="$nomiri"
            echo "ok    $name: applies and compiles, not run ($why); $breaks"
            compiled=$((compiled + 1))
        else
            echo "FAIL  $name: does not compile; $breaks"
            fail=1
        fi
    else
        read -r passed failed <<< "$(run "$@" || true)"
        if [ -n "${failed:-}" ] && [ "$failed" -gt 0 ]; then
            echo "ok    $name: caught ($failed test(s) fail); $breaks"
        else
            echo "FAIL  $name: no test fails; $breaks"
            fail=1
        fi
    fi
    patch -s -p1 -F0 -R --no-backup-if-mismatch -d "$TMP/crate" < "$m"
done
[ "$fail" -eq 0 ] || { echo "check-mutations: FAILED" >&2; exit 1; }
[ "$n" -gt 0 ] || { echo "error: no mutations of $SRC" >&2; exit 1; }
if [ "$compiled" -eq "$n" ]; then
    echo "check-mutations: each of the $n mutations of $SRC applies and compiles; none was run"
elif [ "$compiled" -gt 0 ]; then
    echo "check-mutations: $((n - compiled)) of the $n mutations of $SRC are caught; $compiled only compiled"
else
    echo "check-mutations: each of the $n mutations of $SRC is caught"
fi
