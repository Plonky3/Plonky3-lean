#!/usr/bin/env bash
#
# check-patches.sh -- enforce the patch conventions of docs/patches.md.
#
# Patches are meant to be read one at a time, so every patch carries its own
# rationale in its header. This script is what keeps that promise honest.
#
# Checks, per patch (crates/<crate>/patches/{pre,post}/*.patch, and a
# variant's crates/<crate>/variants/<name>/patches/post/*.patch):
#   - filename is NNN-lowercase-slug.patch
#   - the required header fields are present and non-empty: for every patch
#     Patch, Phase, Target, Hunks, Class, Gap, Cost, Upstreamable, Drop when;
#     for a pre patch also Test and Mutation
#   - `# Patch:` matches the filename stem, `# Phase:` matches the directory
#   - `# Class:` is one of the phase's classes (docs/patches.md)
#   - `# Gap:` cites docs/extractor-issues.md by item number, and each cited
#     item exists; `# Upstreamable:` starts with `yes:` or `no:`
#   - `# Hunks:` matches the actual number of @@ hunks
#   - every file the diff touches is listed in `# Target:`, is relative, and
#     does not escape the phase root
#   - a pre patch has its recorded mutation, `NNN-slug.mutation.patch`
# and per phase:
#   - the whole ordered set applies cleanly (zero fuzz): every crate's `pre`
#     patches together to plonky3/, and each crate's or variant's `post`
#     patches to its pristine hax output, when a run of extract.sh has left one
#   - each mutation applies cleanly on top of the whole `pre` set
#
# Usage: tools/extract/check-patches.sh
set -eu

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
RUST="$ROOT/plonky3"
PRISTINE="${EXTRACT_DIR:-$ROOT/.lake/extract}/pristine"
ISSUES="$ROOT/docs/extractor-issues.md"

REQUIRED=(Patch Phase Target Hunks Class Gap Cost Upstreamable "Drop when")
REQUIRED_PRE=(Test Mutation)
CLASSES_PRE="cfg-hide bound equiv-rewrite"
CLASSES_POST="restore reshape rename"
fail=0
err() { echo "  FAIL: $*" >&2; fail=1; }

field() {   # field <file> <name>  -> value of the field's first line, trimmed
    sed -n "s/^# $2:[[:space:]]*//p" "$1" | head -1 | sed 's/[[:space:]]*$//'
}

field_all() {   # field_all <file> <name>  -> value with its continuation lines
    awk -v n="# $2:" '
        index($0, n) == 1 { sub("^" n "[[:space:]]*", ""); v = $0; on = 1; next }
        on && /^#[[:space:]][[:space:]][[:space:]][[:space:]][[:space:]][[:space:]]+[^[:space:]]/ {
            sub(/^#[[:space:]]+/, ""); v = v " " $0; next }
        { on = 0 }
        END { print v }' "$1"
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

    local f required=("${REQUIRED[@]}")
    [ "$phase" = pre ] && required+=("${REQUIRED_PRE[@]}")
    for f in "${required[@]}"; do
        if [ -z "$(field "$pf" "$f")" ]; then
            err "$base: missing or empty '# $f:' header"
        fi
    done

    [ "$(field "$pf" Patch)" = "$stem" ] || \
        err "$base: '# Patch:' is '$(field "$pf" Patch)', expected '$stem'"
    [ "$(field "$pf" Phase)" = "$phase" ] || \
        err "$base: '# Phase:' is '$(field "$pf" Phase)', expected '$phase'"

    local class classes n
    class="$(field "$pf" Class)"
    [ "$phase" = pre ] && classes="$CLASSES_PRE" || classes="$CLASSES_POST"
    case " $classes " in
        *" $class "*) ;;
        *) err "$base: '# Class: $class' is not a $phase class ($classes)" ;;
    esac
    case "$(field "$pf" Upstreamable)" in
        yes:*|no:*) ;;
        *) err "$base: '# Upstreamable:' must start with 'yes:' or 'no:'" ;;
    esac
    n="$(field_all "$pf" Gap | grep -oE 'extractor-issues\.md [0-9]+' | grep -oE '[0-9]+$' || true)"
    [ -n "$n" ] || err "$base: '# Gap:' must cite docs/extractor-issues.md by item number"
    for f in $n; do
        grep -qE "^$f\. " "$ISSUES" || err "$base: '# Gap:' cites extractor-issues.md $f, which does not exist"
    done
    if [ "$phase" = pre ] && [ ! -f "${pf%.patch}.mutation.patch" ]; then
        err "$base: no recorded mutation ${stem}.mutation.patch (docs/patches.md)"
    fi

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
    for pf in "${pre[@]}"; do
        mf="${pf%.patch}.mutation.patch"
        [ -f "$mf" ] || continue
        echo "  -- dry-run applying $(basename "$mf") on top of them"
        dry_run "$RUST" "${pre[@]}" "$mf"
    done
fi
for mf in "$ROOT"/crates/*/patches/*/*.mutation.patch; do
    [ -e "$mf" ] || continue
    [ -f "${mf%.mutation.patch}.patch" ] && [ "$(basename "$(dirname "$mf")")" = pre ] \
        || err "${mf#"$ROOT"/crates/}: a mutation must sit beside the pre patch it mutates"
    mstem="$(basename "${mf%.mutation.patch}")"
    [ "$(field "$mf" "Mutation of")" = "$mstem" ] \
        || err "${mf#"$ROOT"/crates/}: '# Mutation of:' must be '$mstem'"
    [ -n "$(field "$mf" Breaks)" ] || err "${mf#"$ROOT"/crates/}: missing '# Breaks:'"
done

echo "== post =="
n=0
for dir in "$ROOT"/crates/*/patches/post "$ROOT"/crates/*/variants/*/patches/post; do
    [ -d "$dir" ] || continue
    home="$(dirname "$(dirname "$dir")")"
    case "$home" in
        */variants/*) crate="$(basename "$(dirname "$(dirname "$home")")")@$(basename "$home")" ;;
        *) crate="$(basename "$home")" ;;
    esac
    [ "$crate" != "_template" ] || continue
    post=()
    for pf in "$dir"/[0-9]*.patch; do
        [ -e "$pf" ] || continue
        case "$pf" in *.mutation.patch) continue ;; esac
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
