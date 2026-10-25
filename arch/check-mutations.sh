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
#   - AVX2 (tests/avx2.rs, the mutations of src/x86_64/): an x86_64 build with
#     AVX2, selected by RUSTFLAGS, e.g. `--target x86_64-apple-darwin` under
#     Rosetta:
#       RUSTFLAGS="-C target-feature=+avx2" arch/check-mutations.sh [cargo test args...]
#   - NEON (tests/neon.rs, the mutations of src/aarch64/): an AArch64 host,
#     with RUSTFLAGS not naming AVX2:
#       arch/check-mutations.sh [cargo test args...]
set -eu

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
case "${RUSTFLAGS:-}" in
    *avx2*) SUITE=avx2; SRC=src/x86_64 ;;
    *)
        case "$(rustc -vV | sed -n 's/^host: //p')" in
            aarch64-*) SUITE=neon; SRC=src/aarch64 ;;
            *) echo "error: on x86_64, set RUSTFLAGS=\"-C target-feature=+avx2\" (see the header)" >&2; exit 2 ;;
        esac ;;
esac
echo "suite: tests/$SUITE.rs, the mutations of $SRC/"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$TMP/target}"
rsync -a --exclude target/ --exclude mutations/ "$HERE/" "$TMP/crate/"

run() {   # the differential tests; prints the number that ran
    (cd "$TMP/crate" && cargo test --quiet --locked --release --test "$SUITE" "$@" 2>&1) \
        | sed -n 's/^test result: [A-Za-z]*\. \([0-9]*\) passed; \([0-9]*\) failed.*/\1 \2/p' | tail -1
}

read -r passed failed <<< "$(run "$@")"
if [ "${passed:-0}" -eq 0 ] || [ "${failed:-1}" -ne 0 ]; then
    echo "error: the tests do not pass as written (${passed:-0} passed, ${failed:-?} failed)" >&2
    exit 1
fi
echo "as written: $passed test(s) pass"

fail=0
n=0
for m in "$HERE"/mutations/*.patch; do
    grep -q "^+++ b/$SRC/" "$m" || continue
    n=$((n + 1))
    name="$(basename "$m" .patch)"
    breaks="$(sed -n 's/^# Breaks:[[:space:]]*//p' "$m")"
    patch -s -p1 -F0 --no-backup-if-mismatch -d "$TMP/crate" < "$m"
    read -r passed failed <<< "$(run "$@" || true)"
    patch -s -p1 -F0 -R --no-backup-if-mismatch -d "$TMP/crate" < "$m"
    if [ -n "${failed:-}" ] && [ "$failed" -gt 0 ]; then
        echo "ok    $name: caught ($failed test(s) fail); $breaks"
    else
        echo "FAIL  $name: no test fails; $breaks"
        fail=1
    fi
done
[ "$fail" -eq 0 ] || { echo "check-mutations: FAILED" >&2; exit 1; }
[ "$n" -gt 0 ] || { echo "error: no mutations of $SRC/" >&2; exit 1; }
echo "check-mutations: each of the $n mutations of $SRC/ is caught"
