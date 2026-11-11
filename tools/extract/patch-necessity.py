#!/usr/bin/env python3
"""patch-necessity.py -- is each patch still needed? Leave it out and see.

For each patch (all of them, or those named), runs

    extract.sh --skip-tests --without <crate>/<phase>/<NNN>

in a scratch EXTRACT_DIR and records the first step that fails without it:
the cargo check of the extracted variant (3), charon or aeneas (4), an
`Assumptions/` file against its template (6), another patch that no longer
applies (3 or 7), or `lake build` (8). A patch whose removal fails nothing is
not needed; the record says whether the generated output still changes.

The committed extraction is restored after every run, and extract.sh restores
plonky3/ itself, so the tree ends as it started. Needs a clean
crates/*/extraction/ to start from. This is how a toolchain bump re-justifies
each patch: a patch's header must give the failure this tool records for it.

  patch-necessity.py                       every patch
  patch-necessity.py baby-bear/post/020    only these
  patch-necessity.py --list                print the patch ids
"""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
SPEC = ":(glob)crates/*/extraction/**"
STEPS = {
    "3": "cargo check of the extracted variant (step 3)",
    "4": "charon / aeneas (step 4)",
    "6": "Assumptions/ against the regenerated templates (step 6)",
    "7": "post-extraction patches (step 7)",
    "8": "lake build (step 8)",
}


def patch_ids():
    out = []
    for pf in sorted((ROOT / "crates").glob("*/patches/*/[0-9]*.patch")):
        if pf.name.endswith(".mutation.patch") or pf.parts[-4] == "_template":
            continue
        crate, phase = pf.parts[-4], pf.parts[-2]
        out.append(f"{crate}/{phase}/{pf.name[:3]}")
    return out


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, text=True, capture_output=True, check=True).stdout


def restore():
    git("checkout", "--", SPEC)
    git("clean", "-fdq", "--", SPEC)


def known_warnings():
    return {l for l in (ROOT / "known-warnings.txt").read_text().splitlines()
            if l.strip() and not l.startswith("#")}


def first_failure(log):
    """(step, evidence lines) of a failed run's log: the step it stopped in, then
    the errors it printed, the warnings a gate rejected, and any Lean warning
    known-warnings.txt does not list (one per distinct message, line numbers
    dropped, so a renamed declaration and its uses count once)."""
    lines = [re.sub(r"\x1b\[[0-9;]*m", "", l).rstrip() for l in log.splitlines()]
    step = "?"
    for line in lines:
        m = re.match(r"==> (\d)/8", line)
        if m:
            step = m.group(1)
    known = known_warnings()
    picked = []
    for i, l in enumerate(lines):
        s = l.strip()
        if re.search(r"\[Error\]", s):                      # aeneas
            picked.append(re.sub(r"^.*?\[Error\]\s*", "aeneas: ", s))
        elif re.match(r"error\b", s) and not s.startswith(("error: build failed", "error: lake build failed")):
            picked.append(s)
            if s.endswith("add these warnings:") and i + 1 < len(lines):
                picked.append(lines[i + 1].strip())
        else:
            m = re.match(r"warning: ((?:crates|Plonky3Lean|ToCompPoly)[^:]*):\d+:\d+: (.*)", s)
            if m and f"{m.group(1)}: {m.group(2)}" not in known:
                picked.append(f"warning: {m.group(1)}: {m.group(2)}")
    seen, out = set(), []
    for p in picked:
        key = re.sub(r":\d+:\d+:", ":", p)
        if key not in seen:
            seen.add(key)
            out.append(key)
    if len(out) > 6:
        out = out[:6] + [f"... and {len(out) - 6} more"]
    return step, out


def run(pid, work):
    env = dict(os.environ, EXTRACT_DIR=str(work))
    r = subprocess.run([str(ROOT / "tools/extract/extract.sh"), "--skip-tests", "--without", pid],
                       cwd=ROOT, env=env, text=True, capture_output=True)
    log = r.stdout + r.stderr
    # aeneas truncates what it prints and writes the rest beside its output,
    # which the next run overwrites; keep it with this run's log.
    for full in sorted(work.glob("out/*/aeneas-error.log")):
        log += f"\n--- {full.relative_to(work)}\n" + full.read_text(errors="replace")
        full.unlink()
    (work / f"necessity-{pid.replace('/', '-')}.log").write_text(log)
    if r.returncode == 0:
        changed = git("diff", "--stat", "--", SPEC).strip().splitlines()
        untracked = git("ls-files", "--others", "--exclude-standard", "--", SPEC).split()
        restore()
        if not changed and not untracked:
            return "not needed", ["no step fails, and the generated output is unchanged"]
        return "not needed", ["no step fails; the generated output changes:"] + changed[-6:] + untracked
    step, errs = first_failure(log)
    restore()
    return "needed", [STEPS.get(step, f"step {step}")] + errs


def main(argv):
    if argv == ["--list"]:
        print("\n".join(patch_ids()))
        return
    ids = argv or patch_ids()
    for pid in ids:
        if pid not in patch_ids():
            sys.exit(f"error: no patch {pid}; see --list")
    if git("status", "--porcelain", "--", SPEC).strip():
        sys.exit("error: crates/*/extraction/ has local changes; commit or restore them first")
    work = Path(os.environ.get("EXTRACT_DIR") or tempfile.mkdtemp(prefix="necessity-"))
    work.mkdir(parents=True, exist_ok=True)
    results = []
    for pid in ids:
        print(f"== {pid}: extracting without it", flush=True)
        verdict, why = run(pid, work)
        results.append((pid, verdict, why))
        print(f"   {verdict}: " + "\n     ".join(why), flush=True)
    print("\n| Patch | Without it |\n|---|---|")
    for pid, verdict, why in results:
        print(f"| `{pid}` | {verdict}: " + "; ".join(w.replace("|", "\\|") for w in why) + " |")
    print(f"\nlogs in {work}")


if __name__ == "__main__":
    main(sys.argv[1:])
