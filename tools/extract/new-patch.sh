#!/usr/bin/env bash
#
# new-patch.sh -- capture the current deviation as a new, self-documenting patch.
#
#   tools/extract/new-patch.sh baby-bear post 040-my-fix
#   tools/extract/new-patch.sh baby-bear pre  050-work-around-hax-ice
#
# Patches are hand-owned, not regenerated: this script writes a patch once,
# with a header skeleton to fill in, and never touches existing ones. That is
# what lets each patch carry its own rationale (see check-patches.sh).
#
# post: edit a file under crates/<crate>/extraction/<Lib>/Extraction/, then run
#   this. It rebuilds the baseline (the pristine output of the last extract.sh
#   run, plus the crate's existing post patches) in a temp dir and diffs the
#   live files against it, so the captured delta is ONLY the new change.
# pre: wraps `git diff` in plonky3/. Edit the Rust there, run this, then revert
#   the edit (`git -C plonky3 checkout -- <files>`): extract.sh applies the
#   patch itself.
#
# The new number must sort after every existing patch of the crate's phase,
# because the baseline is "all existing patches applied".
set -eu

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
RUST="$ROOT/plonky3"
PRISTINE="${EXTRACT_DIR:-$ROOT/.lake/extract}/pristine"

if [ "$#" -ne 3 ]; then
    echo "usage: $0 <crate> <pre|post> <NNN-slug>" >&2
    exit 2
fi
CRATE="$1"
PHASE="$2"
STEM="$3"
[ -f "$ROOT/crates/$CRATE/crate.toml" ] || { echo "error: no crates/$CRATE/crate.toml" >&2; exit 2; }
case "$PHASE" in
    pre|post) ;;
    *) echo "error: phase must be pre or post" >&2; exit 2 ;;
esac
if ! printf '%s' "$STEM" | grep -Eq '^[0-9]{3}-[a-z0-9]+(-[a-z0-9]+)*$'; then
    echo "error: '$STEM' must look like 070-lowercase-slug" >&2
    exit 2
fi

DIR="$ROOT/crates/$CRATE/patches/$PHASE"
OUT="$DIR/$STEM.patch"
mkdir -p "$DIR"
[ ! -e "$OUT" ] || { echo "error: $OUT already exists" >&2; exit 1; }

NUM="${STEM%%-*}"
for existing in "$DIR"/[0-9]*.patch; do
    [ -e "$existing" ] || continue
    e="$(basename "$existing")"
    if [ "${e%%-*}" \> "$NUM" ] || [ "${e%%-*}" = "$NUM" ]; then
        echo "error: $e sorts at or after $NUM; pick a higher number." >&2
        echo "       The baseline assumes every existing patch is already applied." >&2
        exit 1
    fi
done

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
RAW="$TMP/raw.diff"

if [ "$PHASE" = "post" ]; then
    [ -d "$PRISTINE/$CRATE" ] || { echo "error: no $PRISTINE/$CRATE; run tools/extract/extract.sh first" >&2; exit 1; }
    mkdir -p "$TMP/base"
    cp -R "$PRISTINE/$CRATE"/. "$TMP/base"/
    for pf in "$DIR"/[0-9]*.patch; do
        [ -e "$pf" ] || continue
        patch -p1 -F0 --no-backup-if-mismatch -d "$TMP/base" < "$pf" >/dev/null \
            || { echo "error: existing $(basename "$pf") no longer applies to the pristine output." >&2
                 echo "       Fix that patch before authoring a new one." >&2; exit 1; }
    done
    (cd "$TMP/base" && find . -name '*.lean' | sed 's|^\./||' | sort) | while read -r f; do
        diff -u -L "a/$f" -L "b/$f" "$TMP/base/$f" "$ROOT/crates/$CRATE/$f" >> "$RAW" || true
    done
else
    ( cd "$RUST" && git diff ) > "$RAW" || true
fi

if [ ! -s "$RAW" ]; then
    echo "error: nothing to capture -- no deviation found." >&2
    [ "$PHASE" = "post" ] \
        && echo "       Edit a generated file first." >&2 \
        || echo "       Edit the Rust in plonky3/ first." >&2
    exit 1
fi

HUNKS="$(grep -c '^@@' "$RAW" || true)"
TARGETS="$(grep '^+++ ' "$RAW" | sed 's/^+++ b\///; s/^+++ //; s/\t.*$//' \
           | paste -sd, - | sed 's/,/, /g')"

{
    printf '# Patch:     %s\n' "$STEM"
    printf '# Phase:     %s\n' "$PHASE"
    printf '# Target:    %s\n' "$TARGETS"
    printf '# Hunks:     %s\n' "$HUNKS"
    printf '# Cost:      TODO -- write "none", or name the axiom/assumption added\n'
    printf '# Upstream:  TODO -- delete this line, or name the upstream bug\n'
    printf '# Drop when: TODO -- the condition under which this patch can be deleted\n'
    printf '#\n'
    printf '# TODO: why this change is necessary, and why it is the least-bad option.\n'
    printf '# A reviewer should be able to judge this patch from its header alone.\n'
    printf '#\n'
    cat "$RAW"
} > "$OUT"

echo "==> wrote ${OUT#"$ROOT"/} ($HUNKS hunk(s), targets: $TARGETS)"
echo "    Now fill in the TODO header fields, then run:"
echo "      tools/extract/check-patches.sh"
