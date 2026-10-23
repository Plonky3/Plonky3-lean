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
#      record every difference in the patch headers (test-pre-patches.py);
#      then show that each pre-patch's own tests pass, and fail under its
#      recorded mutation (check-mutations.py)
#   3. apply every crates/*/patches/pre/ patch to plonky3/, and `cargo check`
#      each extracted crate in the configuration charon sees, for each target
#   4. run `cargo hax into lean` over each crate whose state is `extracted`
#      (whole crate) or `scoped` (rooted at its crate.toml `start_from`), then
#      over each `[[variant]]`, which is renamed to its own library and
#      namespace (rename-variant.py)
#   5. revert the pre-extraction patches (unconditionally, even on failure)
#   6. check each hand-written `Assumptions/*External.lean` against the template
#      aeneas regenerated, install the output into crates/<crate>/extraction/
#      (a variant's into crates/<crate>/variants/<name>/extraction/), snapshot
#      it as the pristine baseline for post-extraction patches, and write
#      its gaps.toml (gap-report.py)
#   7. apply each crate's and variant's patches/post/ patches
#   8. `lake build`, whose warnings must be exactly those in known-warnings.txt
#
# A unit is a crate or a variant (config.py units); `<home>` below is the
# directory holding its extraction/ and patches/post/.
#
# With --check, the run must also leave every extraction/ exactly as
# committed: re-extraction is byte-identical, or the run fails.
#
# --skip-tests skips step 2, and --without <crate>/<phase>/<NNN> (repeatable)
# leaves one patch out of steps 3 and 7. Together they are how
# patch-necessity.py re-justifies each patch; neither belongs in a real run.
#
# Usage:  tools/extract/extract.sh [--tools-only] [--check] [--skip-tests]
#                                  [--without <crate>/<phase>/<NNN>]...
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
SKIP_TESTS=0
WITHOUT=""   # one `<crate>/patches/<phase>/<NNN>-` prefix per line
while [ "$#" -gt 0 ]; do
    case "$1" in
        --tools-only) TOOLS_ONLY=1 ;;
        --check) CHECK=1 ;;
        --skip-tests) SKIP_TESTS=1 ;;
        --without)
            [ "$#" -ge 2 ] || { echo "error: --without needs <crate>/<phase>/<NNN>" >&2; exit 2; }
            case "$2" in
                */pre/[0-9][0-9][0-9]|*/post/[0-9][0-9][0-9]) ;;
                *) echo "error: --without takes <crate>/<phase>/<NNN>, not '$2'" >&2; exit 2 ;;
            esac
            w_crate="${2%%/*}"; w_rest="${2#*/}"
            ls "$ROOT/crates/$w_crate/patches/${w_rest%%/*}/${w_rest##*/}-"*.patch >/dev/null 2>&1 \
                || { echo "error: --without $2: no such patch" >&2; exit 2; }
            WITHOUT="$WITHOUT$w_crate/patches/${w_rest%%/*}/${w_rest##*/}-
"
            shift ;;
        -h|--help) sed -n '2,/^set -eu/p' "$0" | sed '$d; s/^# \{0,1\}//'; exit 0 ;;
        *) echo "error: unknown argument '$1' (try --help)" >&2; exit 2 ;;
    esac
    shift
done
# drop_without <list>: remove the patches named by --without from a list file.
drop_without() {
    [ -n "$WITHOUT" ] || return 0
    local keep pf w skip
    keep="$(mktemp)"
    while read -r pf; do
        skip=0
        while read -r w; do
            [ -n "$w" ] || continue
            case "$pf" in *"/crates/$w"*) skip=1 ;; esac
        done <<< "$WITHOUT"
        if [ "$skip" = "1" ]; then
            echo "    left out: ${pf#"$ROOT"/crates/}"
        else
            echo "$pf" >> "$keep"
        fi
    done < "$1"
    mv "$keep" "$1"
}

tc() { "$CONFIG" toolchain "$1"; }
HAX_RELEASE="$(tc hax_release)"
HAX_COMMIT="$(tc hax_commit)"
if [ -n "$HAX_RELEASE" ]; then
    HAX_NAME="hax $HAX_RELEASE"
    HAX_INSTALL="cargo install --locked cargo-hax@$HAX_RELEASE --force"
    HAX_ID_RE="version=$HAX_RELEASE|commit=$HAX_COMMIT"
else
    HAX_NAME="hax at ${HAX_COMMIT:0:7}"
    HAX_INSTALL="cargo install --locked --git https://github.com/cryspen/hax --rev $HAX_COMMIT cargo-hax --force"
    HAX_ID_RE="commit=$HAX_COMMIT"
fi
EXPECT_CHARON="$(tc charon)"
EXPECT_AENEAS="$(tc aeneas)"
CHARON_TOOLCHAIN="$(tc rust_toolchain)"
CHARON_COMPONENTS="$(tc rust_components | tr ' ' ',')"
HAX_TARGET="$(tc target)"

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
for t in $("$CONFIG" units | cut -d'|' -f1 | grep '@' | while read -r u; do "$CONFIG" target "$u"; done | sort -u); do
    rustup target list --toolchain "$CHARON_TOOLCHAIN" --installed 2>/dev/null | grep -qx "$t" \
        || missing "Rust $CHARON_TOOLCHAIN's $t target, for a variant" \
            "rustup target add --toolchain $CHARON_TOOLCHAIN $t"
    echo "    rust     target $t (variants)"
done

# The `cargo-hax` on PATH is the normal path; HAX_BIN overrides it.
HAX_BIN="${HAX_BIN:-cargo-hax}"
hax_id="$("$HAX_BIN" hax --version 2>/dev/null || true)"
if ! printf '%s\n' "$hax_id" | grep -qxE "$HAX_ID_RE"; then
    if [ -z "$hax_id" ]; then
        echo "error: $HAX_BIN not found." >&2
    else
        echo "error: $HAX_BIN is not $HAX_NAME ($(printf '%s\n' "$hax_id" | grep -m1 '^version=')):" >&2
    fi
    echo "       $HAX_INSTALL" >&2
    exit 1
fi
echo "    hax      $HAX_NAME ($(command -v "$HAX_BIN"))"
# Only a note: a newer release is a reason to bump (docs/runbook.md), not to fail.
latest="$(git ls-remote --tags https://github.com/cryspen/hax 'refs/tags/cargo-hax-v*' 2>/dev/null \
          | sed -n 's#.*refs/tags/cargo-hax-v\([0-9.]*\)$#\1#p' | sort -t. -k1,1n -k2,2n -k3,3n | tail -1)"
if [ -n "$latest" ] && [ "$latest" != "$HAX_RELEASE" ]; then
    echo "    note: hax $latest is the latest release; toolchain.toml pins $HAX_NAME"
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

# Units to extract: every crate whose state is not `stub`, then every variant.
UNITS="$("$CONFIG" units | awk -F'|' '$3 != "stub"')"

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
        if [ -f "$root/$f" ]; then cp "$root/$f" "$scratch/$f"; fi
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
# plonky3/Cargo.lock is not tracked, so no patch edits it, but cargo records
# there the dependencies the pre-patches add. It is restored with the sources.
LOCK_SAVE="$(mktemp)"
revert_pre_patches() {
    [ -s "$PRE_RECORD" ] || return 0
    local ok=1 pf
    for pf in $( (tail -r "$PRE_RECORD" 2>/dev/null || tac "$PRE_RECORD") ); do
        patch $PATCH_FLAGS -R -d "$RUST" < "$pf" >/dev/null || ok=0
    done
    : > "$PRE_RECORD"
    [ ! -s "$LOCK_SAVE" ] || cp "$LOCK_SAVE" "$RUST/Cargo.lock"
    if [ "$ok" = "1" ]; then
        echo "    reverted pre-extraction patches"
    else
        echo "ERROR: could not revert pre-extraction patches. plonky3/ is left" >&2
        echo "       MODIFIED -- inspect 'git -C plonky3 status' before building." >&2
    fi
}
cleanup() { revert_pre_patches; rm -f "$PRE_RECORD" "$PRE_LIST" "$LOCK_SAVE"; }
trap cleanup EXIT

echo "==> 1/8 checking patch conventions"
"$HERE/check-patches.sh"

echo "==> 2/8 upstream tests, with and without the pre-extraction patches"
if [ "$SKIP_TESTS" = "1" ]; then
    echo "    skipped (--skip-tests)"
else
    "$HERE/test-pre-patches.py"
    echo "    -- each pre-patch's tests, and its recorded mutation"
    "$HERE/check-mutations.py"
fi

echo "==> 3/8 pre-extraction patches (plonky3/) and cargo check, per target"
"$CONFIG" pre-patches > "$PRE_LIST"
drop_without "$PRE_LIST"
if [ -s "$PRE_LIST" ]; then
    echo "    WARNING: patching Rust source changes the artifact under" >&2
    echo "             verification. See docs/patches.md." >&2
fi
CHECKS="$("$CONFIG" checks)"
check() {   # check <log>: cargo check of the extracted crates as charon sees them, per target
    local target flags packages
    : > "$1"
    while IFS='|' read -r target flags packages; do
        (cd "$RUST" && env RUSTUP_TOOLCHAIN="$CHARON_TOOLCHAIN" \
            RUSTFLAGS="$flags" CARGO_TARGET_DIR="$WORK/target-check" \
            cargo check --quiet --target "$target" $packages) >> "$1" 2>&1 || return 1
    done <<< "$CHECKS"
}
warnings() {   # the warning headlines of a check log, one per line, sorted
    sed 's/\x1b\[[0-9;]*m//g' "$1" | grep '^warning' | sort || true
}
# Upstream's own warnings, from the tree as pinned: newer cargo lints Plonky3's
# manifests, for example. They are reported, and only warnings the patches add
# fail the run. Headlines are compared, not locations, since a patch may move lines.
base_log="$(mktemp)"
check "$base_log" || true
[ ! -f "$RUST/Cargo.lock" ] || cp "$RUST/Cargo.lock" "$LOCK_SAVE"
apply_set "$PRE_LIST" "$RUST" "$PRE_RECORD"
# If a patch removed something that code reachable from an extracted crate still
# uses, this is where it fails. Warnings count too: a patch that leaves an unused
# import behind is not finished.
check_log="$(mktemp)"
if ! check "$check_log"; then
    cat "$check_log" >&2
    echo "error: the patched tree does not compile; a pre-extraction patch" >&2
    echo "       removed something that is still used." >&2
    rm -f "$check_log" "$base_log"
    exit 1
fi
added="$(comm -13 <(warnings "$base_log") <(warnings "$check_log"))"
n_base="$(warnings "$base_log" | grep -c . || true)"
rm -f "$base_log"
if [ -n "$added" ]; then
    cat "$check_log" >&2
    echo "error: the pre-extraction patches add these warnings:" >&2
    printf '%s\n' "$added" | sed 's/^/       /' >&2
    rm -f "$check_log"
    exit 1
fi
rm -f "$check_log"
echo "    cargo check: ok; the patches add no warnings ($n_base from upstream, also without them)"

echo "==> 4/8 extracting with hax (backend: lean = charon + aeneas)"
# Each crate gets a fresh output directory, so a removed item cannot linger.
# Trust the exit status: aeneas exits non-zero on any translation error, and a
# partial file is not worth building.
rm -rf "$WORK/out"
printf '%s\n' "$UNITS" | while IFS='|' read -r unit lib state home; do
    echo "    $unit ($state, $("$CONFIG" target "$unit")) -> $lib/Extraction/"
    out="$WORK/out/$unit"
    mkdir -p "$out"
    args="$("$CONFIG" charon-args "$unit")"
    # A crate outside the workspace (a dependency, or one of this repository's)
    # is extracted from a copy of its source, so that nothing is written into
    # Cargo's registry or the repository.
    src="$("$CONFIG" source "$unit")"
    feats="$("$CONFIG" features "$unit")"
    case "$src" in
        "$RUST"/*)
           if [ -n "$feats" ]; then
               echo "error: the crate.toml of $unit lists features; only a crate outside" >&2
               echo "       the workspace can have them (docs/extractor-issues.md 90)." >&2
               exit 1
           fi ;;
        *) mkdir -p "$WORK/src"; rm -rf "${WORK:?}/src/$unit"
           rsync -a --exclude target/ "$src/" "$WORK/src/$unit/"; src="$WORK/src/$unit"
           # hax's lean backend does not pass cargo arguments on to charon, so the
           # crate's features become the copy's default features.
           [ -z "$feats" ] || "$HERE/default-features.py" "$src/Cargo.toml" "$feats" ;;
    esac
    # hax's output also goes to a per-unit log, which gap-report.py reads for
    # charon's diagnostics.
    (cd "$src" && RUSTFLAGS="$("$CONFIG" rustflags "$unit")" CARGO_TARGET_DIR="$WORK/target-hax" \
        "$HAX_BIN" hax into --output-dir "$out" lean --charon-args="$args" 2>&1 \
        | tee "$WORK/hax-$unit.log"; exit "${PIPESTATUS[0]}")
    # hax names the library and namespace after the package; a variant gets its own.
    case "$unit" in
        *@*) "$HERE/rename-variant.py" "$out" $("$CONFIG" rename "$unit") ;;
    esac
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
while IFS='|' read -r unit lib state home; do
    gen="$WORK/out/$unit/$lib/Extraction"
    [ -d "$gen" ] || { echo "error: hax wrote no $lib/Extraction/ for $unit" >&2; exit 1; }
    for tpl in "$gen/"*External_Template.lean; do
        [ -e "$tpl" ] || continue
        stub="$(basename "$tpl" _Template.lean)"
        mine="$ROOT/$home/extraction/$lib/Assumptions/$stub.lean"
        rel_mine="$home/extraction/$lib/Assumptions/$stub.lean"
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
done <<< "$UNITS"
[ "$stub_fail" -eq 0 ] || exit 1
rm -rf "$PRISTINE"
while IFS='|' read -r unit lib state home; do
    dest="$ROOT/$home/extraction/$lib"
    rm -rf "$dest/Extraction" "$dest/Extraction.lean"
    mkdir -p "$dest/Extraction" "$PRISTINE/$unit/extraction/$lib/Extraction"
    cp "$WORK/out/$unit/$lib/Extraction"/*.lean "$dest/Extraction/"
    cp "$WORK/out/$unit/$lib/Extraction.lean" "$dest/Extraction.lean"
    cp "$dest/Extraction"/*.lean "$PRISTINE/$unit/extraction/$lib/Extraction/"
    # What charon translated but aeneas did not emit; read by tools/status.py.
    "$HERE/gap-report.py" "$unit" "$WORK/out/$unit/llbc/"*.llbc \
        "$WORK/hax-$unit.log" > "$ROOT/$home/extraction/gaps.toml"
done <<< "$UNITS"
echo "    ok; pristine output in ${PRISTINE#"$ROOT"/}/"

echo "==> 7/8 applying post-extraction patches (generated Lean)"
while IFS='|' read -r unit lib state home; do
    list="$(mktemp)"
    ls "$ROOT/$home/patches/post/"[0-9]*.patch 2>/dev/null \
        | grep -v '\.mutation\.patch$' > "$list" || true
    drop_without "$list"
    [ -s "$list" ] && apply_set "$list" "$ROOT/$home" ""
    rm -f "$list"
done <<< "$UNITS"

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
# Every warning must be listed in known-warnings.txt, and every listed one must
# still occur, so the list cannot go stale. A warning is compared as
# `<file>: <message>`, without its line and column.
seen="$(sed -nE 's/^warning: ([^:]+):[0-9]+:[0-9]+: (.*)$/\1: \2/p' "$build_log" | sort -u)"
known="$(grep -v '^#' "$ROOT/known-warnings.txt" | sed '/^[[:space:]]*$/d' | sort -u)"
rm -f "$build_log"
new_w="$(comm -23 <(printf '%s\n' "$seen" | sed '/^$/d') <(printf '%s\n' "$known" | sed '/^$/d'))"
gone_w="$(comm -13 <(printf '%s\n' "$seen" | sed '/^$/d') <(printf '%s\n' "$known" | sed '/^$/d'))"
if [ -n "$new_w" ] || [ -n "$gone_w" ]; then
    [ -z "$new_w" ] || { echo "error: lake build printed warnings not in known-warnings.txt:" >&2; printf '  %s\n' "$new_w" >&2; }
    [ -z "$gone_w" ] || { echo "error: known-warnings.txt lists warnings the build no longer prints; remove them:" >&2; printf '  %s\n' "$gone_w" >&2; }
    exit 1
fi
n_warn="$(printf '%s\n' "$seen" | sed '/^$/d' | wc -l | tr -d ' ')"
n_sorry=$(cd "$ROOT" && find crates/*/extraction crates/*/variants/*/extraction -path '*/Extraction/*.lean' ! -name '*_Template.lean' \
              | xargs cat | grep -c 'sorry' || true)
n_opaque=$(cd "$ROOT" && find crates/*/extraction crates/*/variants/*/extraction crates/*/stub -path '*/Assumptions/*.lean' -o -path '*/stub/*.lean' \
              | xargs cat | grep -cE '^(noncomputable )?(axiom|opaque) ' || true)
echo "    $n_warn known warning(s); generated code contains $n_sorry 'sorry'; hand-written code declares $n_opaque opaque constant(s)"

if [ "$CHECK" = "1" ]; then
    echo "==> check: re-extraction is byte-identical to the committed output"
    # A glob pathspec: a plain `crates/*/extraction` matches only a path equal to
    # it, never the files under it, and so would compare nothing.
    spec=':(glob)crates/*/extraction/**'
    vspec=':(glob)crates/*/variants/*/extraction/**'
    if ! (cd "$ROOT" && git diff --quiet -- "$spec" "$vspec" \
            && [ -z "$(git ls-files --others --exclude-standard -- "$spec" "$vspec")" ]); then
        (cd "$ROOT" && git status --short -- "$spec" "$vspec") >&2
        echo "error: re-extraction changed the committed output above." >&2
        exit 1
    fi
    echo "    ok"
fi
echo "Done. The extraction type-checks, and so do the proofs about it."
