#!/usr/bin/env bash
#
# check-patches.sh -- enforce the patch conventions of docs/patches.md.
#
# Patches are meant to be read one at a time, so every patch carries its own
# rationale in its header. This script is what keeps that promise honest.
#
# Checks, per patch (crates/<crate>/patches/{pre,post}/*.patch):
#   - filename is NNN-lowercase-slug.patch
#   - the required header fields are present and non-empty
#   - `# Patch:` matches the filename stem, `# Phase:` matches the directory
#   - `# Hunks:` matches the actual number of @@ hunks
#   - every file the diff touches is listed in `# Target:`, is relative, and
#     does not escape the phase root
# and per phase:
#   - the whole ordered set applies cleanly (zero fuzz): every crate's `pre`
#     patches together to plonky3/, and each crate's `post` patches to that
#     crate's pristine hax output, when a run of extract.sh has left one
#
# Usage: tools/extract/check-patches.sh
set -eu

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
RUST="$ROOT/plonky3"
PRISTINE="${EXTRACT_DIR:-$ROOT/.lake/extract}/pristine"

REQUIRED="Patch Phase Target Hunks Cost"
fail=0
err() { echo "  FAIL: $*" >&2; fail=1; }

field() {   # field <file> <name>  -> value, trimmed
    sed -n "s/^# $2:[[:space:]]*//p" "$1" | head -1 | sed 's/[[:space:]]*$//'
}

check_one() {
    local pf="$1" phase="$2" base stem
    base="$(basename "$pf")"
    stem="${base%.patch}"
    echo "  ${pf#"$ROOT"/crates/}"

    case "$base" in
        [0-9][0-9][0-9]-*.patch) ;;
        *) err "$base: name must be NNN-slug.patch" ;;
    esac
    if ! printf '%s' "$stem" | grep -Eq '^[0-9]{3}-[a-z0-9]+(-[a-z0-9]+)*$'; then
        err "$base: slug must be lowercase alphanumeric words separated by '-'"
    fi

    local f
    for f in $REQUIRED; do
        if [ -z "$(field "$pf" "$f")" ]; then
            err "$base: missing or empty '# $f:' header"
        fi
    done

    [ "$(field "$pf" Patch)" = "$stem" ] || \
        err "$base: '# Patch:' is '$(field "$pf" Patch)', expected '$stem'"
    [ "$(field "$pf" Phase)" = "$phase" ] || \
        err "$base: '# Phase:' is '$(field "$pf" Phase)', expected '$phase'"

    # The header must not contain a line that patch would mistake for diff
    # content. The diff may start with git's `diff --git` preamble, so either
    # that or the `--- ` file header ends the prose header.
    local first_diff
    first_diff="$(grep -nE '^(diff --git |--- )' "$pf" | head -1 | cut -d: -f1)"
    if [ -z "$first_diff" ]; then
        err "$base: no '--- ' diff header found"
        return
    fi
    if head -n $((first_diff - 1)) "$pf" | grep -qE '^(\+\+\+|@@)'; then
        err "$base: header contains a line starting with '+++' or '@@'"
    fi
    if head -n $((first_diff - 1)) "$pf" | grep -qvE '^#|^$'; then
        err "$base: header lines must start with '#' or be blank"
    fi

    local declared actual
    declared="$(field "$pf" Hunks)"
    actual="$(grep -c '^@@' "$pf" || true)"
    [ "$declared" = "$actual" ] || \
        err "$base: '# Hunks: $declared' but the diff has $actual"

    # Every touched file must be declared in Target and stay inside the root.
    local tgt p touched
    tgt="$(field "$pf" Target)"
    touched="$(mktemp)"
    grep '^+++ ' "$pf" | sed 's/^+++ b\///; s/^+++ //; s/\t.*$//' > "$touched"
    # Redirection, not a pipe: a pipe would run the loop in a subshell and its
    # `fail=1` would be discarded.
    while read -r p; do
        [ -n "$p" ] || continue
        case "$p" in
            /*|*..*) err "$base: target '$p' is absolute or escapes the root" ;;
        esac
        if ! printf '%s' "$tgt" | tr ',' '\n' \
                | sed 's/^[[:space:]]*//; s/[[:space:]]*$//' | grep -qxF "$p"; then
            err "$base: diff touches '$p', absent from '# Target: $tgt'"
        fi
    done < "$touched"
    rm -f "$touched"
}

# dry_run <root to copy from> <patch>...: apply the patches in order to a
# scratch copy of the files they touch.
dry_run() {
    local root="$1" tmp pf f
    shift
    tmp="$(mktemp -d)"
    for pf in "$@"; do
        grep '^+++ ' "$pf" | sed 's/^+++ b\///; s/^+++ //; s/\t.*$//'
    done | sort -u > "$tmp/.files"
    while read -r f; do
        mkdir -p "$tmp/$(dirname "$f")"
        [ -f "$root/$f" ] && cp "$root/$f" "$tmp/$f"
    done < "$tmp/.files"
    for pf in "$@"; do
        patch -p1 -F0 --no-backup-if-mismatch -d "$tmp" < "$pf" >/dev/null \
            || err "${pf#"$ROOT"/crates/} does not apply"
    done
    rm -rf "$tmp"
}

echo "== pre =="
pre=()
for pf in $("$HERE/config.py" pre-patches); do
    check_one "$pf" pre
    pre+=("$pf")
done
if [ "${#pre[@]}" -eq 0 ]; then
    echo "  (none)"
else
    echo "  -- dry-run applying ${#pre[@]} patch(es) in order to plonky3/"
    dry_run "$RUST" "${pre[@]}"
fi

echo "== post =="
n=0
for dir in "$ROOT"/crates/*/patches/post; do
    crate="$(basename "$(dirname "$(dirname "$dir")")")"
    [ "$crate" != "_template" ] || continue
    post=()
    for pf in "$dir"/[0-9]*.patch; do
        [ -e "$pf" ] || continue
        check_one "$pf" post
        post+=("$pf")
    done
    [ "${#post[@]}" -gt 0 ] || continue
    n=$((n + ${#post[@]}))
    if [ -d "$PRISTINE/$crate" ]; then
        echo "  -- dry-run applying ${#post[@]} patch(es) in order to $crate's pristine output"
        dry_run "$PRISTINE/$crate" "${post[@]}"
    else
        echo "  SKIP dry-run for $crate: no pristine output yet; extract.sh checks again after extracting" >&2
    fi
done
[ "$n" -gt 0 ] || echo "  (none)"

if [ "$fail" -ne 0 ]; then
    echo "check-patches: FAILED" >&2
    exit 1
fi
echo "check-patches: all patches conform"
