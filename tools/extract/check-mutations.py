#!/usr/bin/env python3
"""check-mutations.py -- show that each pre-extraction patch's tests can fail.

Every `patches/pre/NNN-slug.patch` names, in its header, the tests that make
the case that it preserves the normal build (`# Test:`), and it has a recorded
mutation beside it, `NNN-slug.mutation.patch`: a diff, applied on top of all
the pre-patches, that breaks what the patch promises (`# Mutation:` says how).
A test that cannot fail proves nothing, so for each patch this script, on a
scratch copy of plonky3/ with every pre-patch applied:

  1. runs the named tests and requires them to pass;
  2. applies the mutation, runs them again, and requires them to fail;
  3. reverts the mutation.

`# Test:` is a `;`-separated list of entries:

    test <package> <cargo test target args>   e.g. test p3-baby-bear --test pre_patch_020
    lint <package> <lint>                     e.g. lint p3-field unexpected_cfgs

A `test` entry passes when the target builds and every test in it runs and
passes (at least one must run). A `lint` entry runs `cargo check --all-targets`
and passes when the build succeeds and `<lint>` is not reported for
`<package>`. Under the mutation, any failure counts (a compile error in the
test target or one of its dependencies, a failing test, or the lint) and is
reported as such.

Results are cached on the tree state, every pre-patch's diff, the mutations,
the `# Test:` fields, this script and `rustc --version`.

Usage: check-mutations.py [--list] [--no-cache]      (run from anywhere)
  --list  print each patch's tests and mutation, check they are declared and
          present, and run nothing
"""
import hashlib
import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location("tpp", HERE / "test-pre-patches.py")
tpp = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(tpp)

REPO = tpp.REPO
WORK = Path(os.environ.get("EXTRACT_DIR", tpp.ROOT / ".lake" / "extract")) / "mutation"
COMPILE_FAIL = re.compile(r"^error: could not compile `([^`]+)` \(([^)]*)\)", re.M)
RESULT = re.compile(r"^test result: \w+\. (\d+) passed; (\d+) failed", re.M)


def field(header, name):
    """A `# Name:` header field, with its continuation lines joined."""
    out, cur = [], False
    for line in header.splitlines():
        m = re.match(rf"^# {re.escape(name)}:\s*(.*)$", line)
        if m:
            out, cur = [m.group(1)], True
        elif cur and re.match(r"^#\s{6,}\S", line):
            out.append(line[1:].strip())
        else:
            cur = False
        if out and not cur:
            break
    return " ".join(out).strip()


def entries(test_field):
    out = []
    for e in (x.strip() for x in test_field.split(";")):
        if not e:
            continue
        kind, *args = e.split()
        if kind == "test" and len(args) >= 2:
            out.append(("test", args[0], args[1:]))
        elif kind == "lint" and len(args) == 2:
            out.append(("lint", args[0], args[1]))
        else:
            raise ValueError(f"bad `# Test:` entry '{e}'")
    return out


def declared():
    """[(patch, tests, mutation description, mutation file)] for every pre-patch."""
    out, bad = [], []
    for p in tpp.patches():
        header = tpp.split_header(p.read_text())[0]
        mut = p.with_name(p.name.removesuffix(".patch") + ".mutation.patch")
        test, desc = field(header, "Test"), field(header, "Mutation")
        try:
            ts = entries(test)
        except ValueError as e:
            bad.append(f"{p.name}: {e}")
            continue
        if not ts:
            bad.append(f"{p.name}: no `# Test:` entries")
        if not desc:
            bad.append(f"{p.name}: no `# Mutation:` description")
        if not mut.exists():
            bad.append(f"{p.name}: no {mut.name}")
        out.append((p, ts, desc, mut))
    return out, bad


def cargo(tree, args):
    env = dict(os.environ, CARGO_TARGET_DIR=str(WORK / "target"), CARGO_TERM_COLOR="never",
               CARGO_PROFILE_DEV_DEBUG="0", CARGO_PROFILE_TEST_DEBUG="0", CARGO_INCREMENTAL="0")
    r = subprocess.run(["cargo", *args, "--locked"], cwd=tree, env=env, text=True,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    return r.returncode, r.stdout


def run_entry(tree, entry):
    """(passed, what happened)."""
    kind, pkg, arg = entry
    if kind == "test":
        code, log = cargo(tree, ["test", "-p", pkg, *arg, "--no-fail-fast"])
        m = COMPILE_FAIL.search(log)
        if m:
            where = "the test target" if m.group(1) == pkg and "test" in m.group(2) else "a dependency"
            return False, f"compile error in {where}: `{m.group(1)}` ({m.group(2)})"
        passed = sum(int(a) for a, _ in RESULT.findall(log))
        failed = sum(int(b) for _, b in RESULT.findall(log))
        if failed or code != 0:
            return False, f"runtime: {failed} test(s) failed"
        if passed == 0:
            return False, "no test ran (wrong target or name?)"
        return True, f"{passed} test(s) passed"
    code, log = cargo(tree, ["check", "-p", pkg, "--all-targets", "--message-format=json"])
    hits = 0
    for line in log.splitlines():
        if not line.startswith("{"):
            continue
        msg = json.loads(line)
        if msg.get("reason") != "compiler-message":
            continue
        c = (msg["message"].get("code") or {}).get("code")
        if c == arg and f"/{pkg}" in msg.get("package_id", "").replace("#", "/"):
            hits += 1
    if code != 0:
        m = COMPILE_FAIL.search(log)
        return False, f"compile error: `{m.group(1)}` ({m.group(2)})" if m else "cargo check failed"
    if hits:
        return False, f"lint: `{arg}` reported {hits} time(s) in {pkg}"
    return True, f"`{arg}` not reported in {pkg}"


def cache_key(decl):
    h = hashlib.sha256()
    h.update(tpp.sh(["git", "ls-tree", "-r", "HEAD"], cwd=REPO).stdout.encode())
    h.update(tpp.sh(["git", "diff", "HEAD"], cwd=REPO).stdout.encode())
    for p, ts, _, mut in decl:
        h.update(p.name.encode())
        h.update(tpp.split_header(p.read_text())[1].encode())
        h.update(repr(ts).encode())
        h.update(mut.read_bytes() if mut.exists() else b"")
    h.update(Path(__file__).read_bytes())
    h.update(tpp.sh(["rustc", "--version"], cwd=REPO).stdout.encode())
    return h.hexdigest()[:16]


def patch(tree, pf, reverse=False):
    args = ["patch", "-p1", "-F0", "--no-backup-if-mismatch", "-s", "-d", str(tree)]
    r = subprocess.run(args + (["-R"] if reverse else []), stdin=open(pf), text=True,
                       capture_output=True)
    return r.returncode == 0, r.stdout + r.stderr


def main():
    decl, bad = declared()
    if "--list" in sys.argv:
        for p, ts, desc, mut in decl:
            print(f"    {p.name}")
            for t in ts:
                print(f"      {t[0]:4} {t[1]} {' '.join(t[2]) if t[0] == 'test' else t[2]}")
            print(f"      mutation: {mut.name}{'' if mut.exists() else ' (MISSING)'}: {desc}")
    for b in bad:
        print(f"    ERROR: {b}")
    if bad:
        return 1
    if "--list" in sys.argv or not decl:
        if not decl:
            print("    no pre-extraction patches; nothing to check")
        return 0

    WORK.mkdir(parents=True, exist_ok=True)
    key = cache_key(decl)
    cache = WORK / f"result-{key}.json"
    if cache.exists() and "--no-cache" not in sys.argv:
        res = json.loads(cache.read_text())
        print(f"    cached ({key})")
    else:
        tree = WORK / "tree"
        tpp.sync(tree)
        tpp.apply(tree, [p for p, *_ in decl])
        res = {}
        for p, ts, desc, mut in decl:
            r = {"clean": [], "mutated": []}
            for t in ts:
                r["clean"].append(run_entry(tree, t))
            ok, out = patch(tree, mut)
            if not ok:
                r["error"] = f"{mut.name} does not apply on top of the pre-patches: {out.strip()}"
            else:
                for t in ts:
                    r["mutated"].append(run_entry(tree, t))
                ok, out = patch(tree, mut, reverse=True)
                if not ok:
                    sys.exit(f"error: could not revert {mut.name}: {out}")
            res[str(p)] = r  # crates share patch names, so key by path
        cache.write_text(json.dumps(res, indent=1))

    fail = False
    for p, ts, desc, mut in decl:
        r = res[str(p)]
        print(f"    {p.name}")
        if "error" in r:
            print(f"      ERROR: {r['error']}")
            fail = True
            continue
        for t, (ok, what) in zip(ts, r["clean"]):
            print(f"      {'ok  ' if ok else 'FAIL'} as patched: {t[0]} {t[1]}: {what}")
            fail |= not ok
        caught = [what for ok, what in r["mutated"] if not ok]
        if caught:
            print(f"      ok   mutated ({desc}): caught, {'; '.join(caught)}")
        else:
            print(f"      FAIL mutated ({desc}): every test still passes, so they cannot "
                  "detect what the mutation breaks")
            fail = True
    print("    check-mutations: " + ("FAILED" if fail else
          f"{len(decl)} patch(es), each with tests that pass and that its mutation fails"))
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
