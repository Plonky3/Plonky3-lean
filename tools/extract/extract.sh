#!/usr/bin/env bash
#
# extract.sh -- regenerate every extracted crate's Lean from the Rust in
# plonky3/, with hax's lean backend (charon + aeneas), and check the result.
#
# The generated Lean is committed (crates/<crate>/extraction/<Lib>/Extraction/),
# so `lake build` alone checks the proofs; this script is how that output is
# produced and how it is shown to be reproducible. It is the interim form of
# `xtask extract` and `xtask check` (tools/README.md).
#
#   0. tools: check (never install) the pins in toolchain.toml: cargo-hax is the
#      pinned release, it resolves and has fetched the pinned charon and aeneas,
#      charon's Rust toolchain is present, and lakefile.toml and lean-toolchain
#      agree with what hax resolves
#   1. check the patch conventions (check-patches.sh)
#   2. run upstream's tests with and without the pre-extraction patches, and
#      record every difference in the patch headers (test-pre-patches.py)
#   3. apply every crates/*/patches/pre/ patch to plonky3/, and `cargo check`
#      each extracted crate in the variant charon sees
#   4. run `cargo hax into lean` over each crate whose state is `extracted`
#      (whole crate) or `scoped` (rooted at its crate.toml `start_from`)
#   5. revert the pre-extraction patches (unconditionally, even on failure)
#   6. check each hand-written `Assumptions/*External.lean` against the template
#      aeneas regenerated, install the output into crates/<crate>/extraction/,
#      and snapshot it as the pristine baseline for post-extraction patches
#   7. apply each crate's patches/post/ patches
#   8. `lake build`, which must be warning-free
#
# With --check, the run must also leave crates/*/extraction/ exactly as
# committed: re-extraction is byte-identical, or the run fails.
#
# Usage:  tools/extract/extract.sh [--tools-only] [--check]
#
# Environment:
#   HAX_BIN      the cargo-hax to use (default: `cargo-hax` on PATH)
#   EXTRACT_DIR  scratch space (default: .lake/extract). Holds the hax output,
#                the pristine snapshot, cargo's target dirs and the cached
#                upstream test results.
set -eu

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
RUST="$ROOT/plonky3"
CONFIG="$HERE/config.py"
WORK="${EXTRACT_DIR:-$ROOT/.lake/extract}"
PRISTINE="$WORK/pristine"
export EXTRACT_DIR="$WORK"

TOOLS_ONLY=0
CHECK=0
for arg in "$@"; do
    case "$arg" in
        --tools-only) TOOLS_ONLY=1 ;;
        --check) CHECK=1 ;;
        -h|--help) sed -n '2,/^set -eu/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
        *) echo "error: unknown argument '$arg' (try --help)" >&2; exit 2 ;;
    esac
done

tc() { "$CONFIG" toolchain "$1"; }
HAX_VERSION="$(tc hax_version)"
HAX_COMMIT="$(tc hax_commit)"
EXPECT_CHARON="$(tc charon)"
EXPECT_AENEAS="$(tc aeneas)"
CHARON_TOOLCHAIN="$(tc rust_toolchain)"
CHARON_COMPONENTS="$(tc rust_components | tr ' ' ',')"
HAX_TARGET="$(tc target)"
EXTRACT_RUSTFLAGS="$(tc rustflags)"

# --- 0. tools -----------------------------------------------------------------
echo "==> 0/8 tools"
missing() {   # missing <what> <install command>
    echo "error: $1 is missing. Install it (see docs/extracting.md):" >&2
    echo "       $2" >&2
    exit 1
}
for cmd in rustup cargo lake python3 rsync patch git; do
    command -v "$cmd" >/dev/null 2>&1 || missing "'$cmd'" "see the requirements table"
done
[ -f "$RUST/Cargo.toml" ] || missing "the plonky3/ submodule" "git submodule update --init"

rustup target list --toolchain "$CHARON_TOOLCHAIN" --installed 2>/dev/null \
        | grep -qx "$HAX_TARGET" \
    && rustup component list --toolchain "$CHARON_TOOLCHAIN" --installed 2>/dev/null \
        | grep -q '^rustc-dev' \
    || missing "Rust $CHARON_TOOLCHAIN with $CHARON_COMPONENTS and $HAX_TARGET" \
        "rustup toolchain install $CHARON_TOOLCHAIN --profile minimal --component $CHARON_COMPONENTS --target $HAX_TARGET"
echo "    rust     $CHARON_TOOLCHAIN (for charon), target $HAX_TARGET"

HAX_BIN="${HAX_BIN:-cargo-hax}"
hax_id="$("$HAX_BIN" hax --version 2>/dev/null || true)"
if ! printf '%s\n' "$hax_id" | grep -qxE "version=$HAX_VERSION|commit=$HAX_COMMIT"; then
    if [ -z "$hax_id" ]; then
        echo "error: $HAX_BIN not found." >&2
    else
        echo "error: $HAX_BIN is not hax $HAX_VERSION ($(printf '%s\n' "$hax_id" | grep -m1 '^version=')):" >&2
    fi
    echo "       cargo install --locked cargo-hax@$HAX_VERSION --force" >&2
    exit 1
fi
echo "    hax      $HAX_VERSION ($(command -v "$HAX_BIN"))"
# Only a note: a newer release is a reason to bump (docs/runbook.md), not to fail.
latest="$(git ls-remote --tags https://github.com/cryspen/hax 'refs/tags/cargo-hax-v*' 2>/dev/null \
          | sed -n 's#.*refs/tags/cargo-hax-v\([0-9.]*\)$#\1#p' | sort -t. -k1,1n -k2,2n -k3,3n | tail -1)"
if [ -n "$latest" ] && [ "$latest" != "$HAX_VERSION" ]; then
    echo "    note: hax $latest is released; toolchain.toml pins $HAX_VERSION"
fi

# charon and aeneas: hax resolves the pinned versions and has fetched them. The
# Lean side must agree too: the generated code and the Lean libraries it imports
# come from one aeneas build.
shown="$(cd "$RUST" && "$HAX_BIN" hax tools show)"
fetched="$("$HAX_BIN" hax tools list 2>/dev/null)"
for tool in "charon $EXPECT_CHARON" "aeneas $EXPECT_AENEAS"; do
    printf '%s\n' "$fetched" | awk -v t="${tool%% *}:" -v v="${tool#* }" \
        '$1 == t { in_t = 1; next } /^[a-z]+:$/ { in_t = 0 }
         in_t && $1 == v && /installed/ { found = 1 } END { exit !found }' \
        || missing "hax's ${tool%% *} ${tool#* }" "(cd plonky3 && cargo hax tools install)"
done
resolved() { printf '%s\n' "$shown" | awk -v t="$1" '$1 == t { print $2; exit }'; }
lake_rev() {   # the `rev` of the [[require]] named $1 in lakefile.toml
    awk -v n="$1" '/^\[\[require\]\]/ { hit = 0 }
                   $0 ~ "^name = \"" n "\"" { hit = 1 }
                   hit && /^rev = / { gsub(/"/, "", $3); print $3; exit }' "$ROOT/lakefile.toml"
}
pin_fail=0
check_pin() {   # check_pin <what> <actual> <expected>
    if [ "$2" != "$3" ]; then
        echo "error: $1 is '$2', expected '$3'." >&2
        pin_fail=1
    fi
}
check_pin "charon (cargo hax tools show)" "$(resolved charon)" "$EXPECT_CHARON"
check_pin "aeneas (cargo hax tools show)" "$(resolved aeneas)" "$EXPECT_AENEAS"
check_pin "lakefile.toml's aeneas rev" "$(lake_rev aeneas)" "$(resolved aeneas)"
check_pin "lakefile.toml's hax rev" "$(lake_rev hax)" "$(resolved hax-lean-lib)"
check_pin "lean-toolchain" "$(cat "$ROOT/lean-toolchain")" "$(resolved lean)"
if [ "$pin_fail" -ne 0 ]; then
    echo "       Look for a hax.toml above plonky3/, or move the pins in" >&2
    echo "       toolchain.toml, lakefile.toml and lean-toolchain together" >&2
    echo "       (docs/runbook.md)." >&2
    exit 1
fi
echo "    charon   $EXPECT_CHARON, aeneas $EXPECT_AENEAS"
echo "    lean     $(cat "$ROOT/lean-toolchain")"
[ "$TOOLS_ONLY" = "0" ] || exit 0

# Crates to extract: every crate whose state is not `stub`.
CRATES="$("$CONFIG" crates | awk -F'|' '$3 != "stub"')"

# --- the patch applier, shared by both phases ---------------------------------
# `patch -F0` forbids fuzz: context drift fails loudly instead of applying
# somewhere merely plausible. Line-number offsets are still tolerated.
PATCH_FLAGS="-p1 -F0 --no-backup-if-mismatch"

# Dry-run the whole ordered set on a scratch copy of the files it touches, then
# apply it. $1 = file listing the patches in order, $2 = root to apply in,
# $3 = file recording what was applied (or "").
apply_set() {
    local list="$1" root="$2" record="$3" pf scratch
    if [ ! -s "$list" ]; then
        echo "    none"
        return 0
    fi
    scratch="$(mktemp -d)"
    while read -r pf; do
        grep '^+++ ' "$pf" | sed 's/^+++ b\///; s/^+++ //; s/\t.*$//'
    done < "$list" | sort -u | while read -r f; do
        mkdir -p "$scratch/$(dirname "$f")"
        [ -f "$root/$f" ] && cp "$root/$f" "$scratch/$f"
    done
    while read -r pf; do
        if ! patch $PATCH_FLAGS -d "$scratch" < "$pf" >/dev/null 2>&1; then
            echo "error: ${pf#"$ROOT"/} does not apply cleanly." >&2
            echo "       Nothing has been changed. Run tools/extract/check-patches.sh" >&2
            echo "       to see the rejects, or fix that patch." >&2
            rm -rf "$scratch"
            return 1
        fi
    done < "$list"
    rm -rf "$scratch"
    while read -r pf; do
        patch $PATCH_FLAGS -d "$root" < "$pf" >/dev/null
        [ -z "$record" ] || echo "$pf" >> "$record"
        printf '    %-62s %s\n' "${pf#"$ROOT"/crates/}" "[$(sed -n 's/^# Cost:[[:space:]]*//p' "$pf" | head -1)]"
    done < "$list"
}

# Reverted on EXIT so an aborted run never leaves plonky3/ modified. We reverse
# exactly what we applied, in reverse order -- never `git checkout`, which would
# discard unrelated work in the submodule. The record is a file rather than a
# bash array because macOS still ships bash 3.2.
PRE_RECORD="$(mktemp)"
PRE_LIST="$(mktemp)"
revert_pre_patches() {
    [ -s "$PRE_RECORD" ] || return 0
    local ok=1 pf
    for pf in $( (tail -r "$PRE_RECORD" 2>/dev/null || tac "$PRE_RECORD") ); do
        patch $PATCH_FLAGS -R -d "$RUST" < "$pf" >/dev/null || ok=0
    done
    : > "$PRE_RECORD"
    if [ "$ok" = "1" ]; then
        echo "    reverted pre-extraction patches"
    else
        echo "ERROR: could not revert pre-extraction patches. plonky3/ is left" >&2
        echo "       MODIFIED -- inspect 'git -C plonky3 status' before building." >&2
    fi
}
cleanup() { revert_pre_patches; rm -f "$PRE_RECORD" "$PRE_LIST"; }
trap cleanup EXIT

echo "==> 1/8 checking patch conventions"
"$HERE/check-patches.sh"

echo "==> 2/8 upstream tests, with and without the pre-extraction patches"
"$HERE/test-pre-patches.py"

echo "==> 3/8 pre-extraction patches (plonky3/) and cargo check ($HAX_TARGET, $EXTRACT_RUSTFLAGS)"
"$CONFIG" pre-patches > "$PRE_LIST"
if [ -s "$PRE_LIST" ]; then
    echo "    WARNING: patching Rust source changes the artifact under" >&2
    echo "             verification. See docs/patches.md." >&2
fi
apply_set "$PRE_LIST" "$RUST" "$PRE_RECORD"
# If a patch removed something that code reachable from an extracted crate still
# uses, this is where it fails. Warnings count too: a patch that leaves an unused
# import behind is not finished.
check_log="$(mktemp)"
packages="$(printf '%s\n' "$CRATES" | cut -d'|' -f1 | sed 's/^/-p p3-/' | tr '\n' ' ')"
if ! (cd "$RUST" && env RUSTUP_TOOLCHAIN="$CHARON_TOOLCHAIN" \
        RUSTFLAGS="$EXTRACT_RUSTFLAGS" CARGO_TARGET_DIR="$WORK/target-check" \
        cargo check --quiet --target "$HAX_TARGET" $packages) > "$check_log" 2>&1; then
    cat "$check_log" >&2
    echo "error: the patched tree does not compile; a pre-extraction patch" >&2
    echo "       removed something that is still used." >&2
    rm -f "$check_log"
    exit 1
fi
if grep -q '^warning' "$check_log"; then
    cat "$check_log" >&2
    echo "error: the patched tree compiles with warnings." >&2
    rm -f "$check_log"
    exit 1
fi
rm -f "$check_log"
echo "    cargo check: ok, 0 warnings"

echo "==> 4/8 extracting with hax (backend: lean = charon + aeneas, target: $HAX_TARGET)"
# Each crate gets a fresh output directory, so a removed item cannot linger.
# Trust the exit status: aeneas exits non-zero on any translation error, and a
# partial file is not worth building.
rm -rf "$WORK/out"
printf '%s\n' "$CRATES" | while IFS='|' read -r crate lib state; do
    echo "    $crate ($state) -> $lib/Extraction/"
    out="$WORK/out/$crate"
    mkdir -p "$out"
    args="$("$CONFIG" charon-args "$crate")"
    (cd "$RUST/$crate" && RUSTFLAGS="$EXTRACT_RUSTFLAGS" CARGO_TARGET_DIR="$WORK/target-hax" \
        "$HAX_BIN" hax into --output-dir "$out" lean --charon-args="$args")
done

# Revert now, before the Lean build, so the rest of the run sees a clean tree.
# The EXIT trap stays armed and becomes a no-op.
echo "==> 5/8 restoring plonky3/"
revert_pre_patches

echo "==> 6/8 checking each Assumptions/ against the regenerated templates; installing"
# aeneas emits `Extraction/<X>External_Template.lean`, the declarations the
# generated code expects someone to supply. Each hand-written
# `Assumptions/<X>External.lean` must declare exactly the names the template
# does. The signatures may differ on purpose; `lake build` checks those. A file
# that states an `axiom` is refused: assumptions here are `opaque` constants.
decl_names() {
    [ -f "$1" ] || return 0
    sed -nE 's/^(noncomputable )?(axiom|opaque|def|abbrev|structure|inductive|class) ([^ :({]+).*/\3/p' "$1" | sort -u
}
stub_fail=0
while IFS='|' read -r crate lib state; do
    gen="$WORK/out/$crate/$lib/Extraction"
    [ -d "$gen" ] || { echo "error: hax wrote no $lib/Extraction/ for $crate" >&2; exit 1; }
    for tpl in "$gen/"*External_Template.lean; do
        [ -e "$tpl" ] || continue
        stub="$(basename "$tpl" _Template.lean)"
        mine="$ROOT/crates/$crate/extraction/$lib/Assumptions/$stub.lean"
        rel_mine="crates/$crate/extraction/$lib/Assumptions/$stub.lean"
        if [ ! -f "$mine" ]; then
            echo "error: $rel_mine is missing. Write it from $stub""_Template.lean," >&2
            echo "       with each hole an \`opaque\` constant." >&2
            stub_fail=1
            continue
        fi
        if grep -qE '^axiom ' "$mine"; then
            echo "error: $rel_mine states an axiom; make it an \`opaque\` constant." >&2
            stub_fail=1
            continue
        fi
        if [ "$(decl_names "$tpl")" != "$(decl_names "$mine")" ]; then
            echo "error: $rel_mine is out of date with the extraction:" >&2
            diff <(decl_names "$tpl") <(decl_names "$mine") \
                | sed -n 's/^< /         needed, not declared: /p; s/^> /         declared, no longer needed: /p' >&2
            stub_fail=1
        fi
    done
done <<< "$CRATES"
[ "$stub_fail" -eq 0 ] || exit 1
rm -rf "$PRISTINE"
while IFS='|' read -r crate lib state; do
    dest="$ROOT/crates/$crate/extraction/$lib"
    rm -rf "$dest/Extraction" "$dest/Extraction.lean"
    mkdir -p "$dest/Extraction" "$PRISTINE/$crate/extraction/$lib/Extraction"
    cp "$WORK/out/$crate/$lib/Extraction"/*.lean "$dest/Extraction/"
    cp "$WORK/out/$crate/$lib/Extraction.lean" "$dest/Extraction.lean"
    cp "$dest/Extraction"/*.lean "$PRISTINE/$crate/extraction/$lib/Extraction/"
done <<< "$CRATES"
echo "    ok; pristine output in ${PRISTINE#"$ROOT"/}/"

echo "==> 7/8 applying post-extraction patches (generated Lean)"
while IFS='|' read -r crate lib state; do
    list="$(mktemp)"
    ls "$ROOT/crates/$crate/patches/post/"[0-9]*.patch > "$list" 2>/dev/null || true
    [ -s "$list" ] && apply_set "$list" "$ROOT/crates/$crate" ""
    rm -f "$list"
done <<< "$CRATES"

echo "==> 8/8 lake build"
# Aeneas's Lean library pulls in mathlib; without the prebuilt cache this is an
# hours-long from-source build.
if [ ! -f "$ROOT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" ]; then
    (cd "$ROOT" && lake exe cache get >/dev/null 2>&1) || \
        echo "note: 'lake exe cache get' failed; mathlib may build from source" >&2
fi
build_log="$(mktemp)"
if ! (cd "$ROOT" && lake build 2>&1 | tee "$build_log"; exit "${PIPESTATUS[0]}"); then
    echo "error: lake build failed. The patched files are in place in each" >&2
    echo "       extraction/; inspect for drift. Fix the failing patch, or author" >&2
    echo "       a new one with tools/extract/new-patch.sh." >&2
    rm -f "$build_log"
    exit 1
fi
n_warn="$(grep -c '^warning' "$build_log" || true)"
rm -f "$build_log"
if [ "$n_warn" -ne 0 ]; then
    echo "error: lake build printed $n_warn warning(s); the build must be warning-free." >&2
    exit 1
fi
n_sorry=$(cd "$ROOT" && find crates/*/extraction -path '*/Extraction/*.lean' ! -name '*_Template.lean' \
              | xargs cat | grep -c 'sorry' || true)
n_opaque=$(cd "$ROOT" && find crates/*/extraction crates/*/stub -path '*/Assumptions/*.lean' -o -path '*/stub/*.lean' \
              | xargs cat | grep -cE '^(noncomputable )?(axiom|opaque) ' || true)
echo "    0 warnings; generated code contains $n_sorry 'sorry'; hand-written code declares $n_opaque opaque constant(s)"

if [ "$CHECK" = "1" ]; then
    echo "==> check: re-extraction is byte-identical to the committed output"
    if ! (cd "$ROOT" && git diff --quiet -- crates/'*'/extraction \
            && [ -z "$(git ls-files --others --exclude-standard -- crates/'*'/extraction)" ]); then
        (cd "$ROOT" && git status --short -- crates/'*'/extraction) >&2
        echo "error: re-extraction changed the committed output above." >&2
        exit 1
    fi
    echo "    ok"
fi
echo "Done. The extraction type-checks, and so do the proofs about it."
