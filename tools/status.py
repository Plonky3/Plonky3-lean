#!/usr/bin/env python3
"""status.py -- generate STATUS.md, the inventory of what the claims rest on.

STATUS.md is generated, never edited by hand. Its inputs are all committed: the
`plonky3/` pin, toolchain.toml, crates/*/crate.toml, each crate's Lean files, the
extraction reports crates/*/extraction/gaps.toml (written by extract.sh), the
patch headers and claims.toml. A Lean pass over the built environment supplies
the claims and their axioms, every `opaque` constant with its docstring, and how
many claims reach each opaque constant and each transcription. So CI regenerates
STATUS.md without the extractor, and fails if the committed one differs.

Every `opaque` constant's docstring must give its reason in a sentence starting
"Assumed"; that sentence is the table's "Why" column.

Run after `lake build`.

  tools/status.py           write STATUS.md
  tools/status.py --check   write nothing; fail if STATUS.md is out of date
"""
import importlib.util
import json
import re
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

sys.dont_write_bytecode = True  # importing check-claims.py must not leave __pycache__/
ROOT = Path(__file__).resolve().parents[1]
CLAIMS_PREFIX = "Plonky3Lean.Claims."

# Warnings from pinned dependencies that the build tolerates. None today; if one
# appears, it is listed here with its reason, and so in STATUS.md.
UPSTREAM_WARNINGS = []


def load_check_claims():
    spec = importlib.util.spec_from_file_location("check_claims", ROOT / "tools/check-claims.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def sh(*args, cwd=ROOT):
    return subprocess.run(args, cwd=cwd, text=True, capture_output=True, check=True).stdout.strip()


def crates():
    out = []
    for d in sorted((ROOT / "crates").iterdir()):
        f = d / "crate.toml"
        if d.name.startswith("_") or not f.is_file():
            continue
        out.append((d.name, tomllib.loads(f.read_text())))
    return out


def lines(paths):
    return sum(len(p.read_text().splitlines()) for p in paths)


def lean_files(name, c):
    """(generated, hand-written) .lean files of a crate's library."""
    d = ROOT / "crates" / name / ("stub" if c["state"] == "stub" else "extraction")
    lib = c["lean_lib"]
    gen = [d / lib / "Extraction" / f for f in ("Types.lean", "Funs.lean")]
    gen = [p for p in gen if p.is_file()]
    hand = sorted(p for p in d.rglob("*.lean") if "/Extraction/" not in p.as_posix())
    return gen, hand


def header(pf):
    """The `# Field:` values of a patch header, continuation lines joined."""
    fields, cur = {}, None
    for line in pf.read_text().splitlines():
        if line.startswith("diff --git ") or line.startswith("--- "):
            break
        m = re.match(r"^# ([A-Z][A-Za-z ]*):\s*(.*)$", line)
        if m:
            cur = m.group(1)
            fields[cur] = m.group(2).strip()
        elif cur and re.match(r"^#\s{3,}\S", line):
            fields[cur] += " " + line[1:].strip()
        else:
            cur = None
    return fields


def patches(name):
    out = []
    for phase in ("pre", "post"):
        for pf in sorted((ROOT / "crates" / name / "patches" / phase).glob("[0-9]*.patch")):
            out.append((phase, pf, header(pf)))
    return out


def has_cost(cost):
    return not re.match(r"^none(\.|$)", cost.strip())


def gaps(name):
    f = ROOT / "crates" / name / "extraction" / "gaps.toml"
    return tomllib.loads(f.read_text()) if f.is_file() else None


def mirror_key(rust):
    """A [[mirror]] Rust path in the form gap-report.py renders items in."""
    parts, depth, cur = [], 0, ""
    for ch in rust:
        depth += ch == "{"
        depth -= ch == "}"
        if ch == ":" and depth == 0 and cur.endswith(":"):
            parts.append(cur[:-1])
            cur = ""
        else:
            cur += ch
    parts.append(cur)
    out = []
    for p in parts:
        m = re.match(r"^\{impl (.+?) for (.+)\}$", p)
        if m:
            self_ty = re.sub(r"<.*>$", "", m.group(2)).split("::")
            out += self_ty[:-1] + ["{impl " + m.group(1) + "}"]
        else:
            out.append(p)
    # An inherent method `Type::f` is rendered `{impl}::f`.
    if len(out) >= 2 and out[-2][:1].isupper() and not out[-2].startswith("{"):
        out[-2] = "{impl}"
    return "::".join(out)


LEAN_QUERY = """\
import Plonky3Lean
open Lean Elab Command

partial def closure (env : Environment) (start : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := #[start]
  while h : todo.size > 0 do
    let n := todo.back
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for c in ci.type.getUsedConstants do todo := todo.push c
      if let some v := ci.value? (allowOpaque := true) then
        for c in v.getUsedConstants do todo := todo.push c
  return seen

#eval show CommandElabM Unit from do
  let env ← getEnv
  let libs : List String := LIBS
  let claims : List Name := CLAIMS
  let mirrors : List Name := MIRRORS
  let inLib (n : Name) : Bool := match env.getModuleIdxFor? n with
    | some i => libs.any fun l => (env.header.moduleNames[i.toNat]!).toString.startsWith l
    | none => false
  let opaques := env.constants.toList.filterMap fun (n, ci) =>
    if ci matches .opaqueInfo _ && inLib n && !n.isInternal then some n else none
  let closures := claims.map (closure env)
  let count (t : Name) : Nat := (closures.filter (·.contains t)).length
  for n in opaques do
    let doc := (← findDocString? env n).getD ""
    let m := match env.getModuleIdxFor? n with
      | some i => (env.header.moduleNames[i.toNat]!).toString
      | none => ""
    IO.println (Json.compress (Json.mkObj [("kind", "opaque"), ("name", toString n),
      ("module", m), ("doc", doc), ("reach", count n)]))
  for n in mirrors do
    IO.println (Json.compress (Json.mkObj [("kind", "mirror"), ("name", toString n),
      ("exists", (env.find? n).isSome), ("reach", count n)]))
"""


def lean_facts(libs, claims, mirrors):
    q = lambda xs: "[" + ", ".join(f"`{x}" for x in xs) + "]"
    src = (LEAN_QUERY.replace("LIBS", "[" + ", ".join(json.dumps(x) for x in libs) + "]")
           .replace("CLAIMS", q(claims)).replace("MIRRORS", q(mirrors)))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(src)
    try:
        r = subprocess.run(["lake", "env", "lean", f.name], cwd=ROOT, text=True,
                           capture_output=True)
    finally:
        Path(f.name).unlink()
    if r.returncode != 0:
        sys.exit(f"error: the Lean pass failed (run `lake build` first?):\n{r.stdout}{r.stderr}")
    return [json.loads(line) for line in r.stdout.splitlines() if line.startswith("{")]


def assumed(doc, name):
    m = re.search(r"Assumed\b[:,]?\s*(.*?)(?:\.\s|\.$|$)", " ".join(doc.split()))
    if not m or not m.group(1):
        sys.exit(f"error: the docstring of opaque `{name}` gives no reason in a sentence "
                 f"starting \"Assumed\"")
    return m.group(1).strip()


def generate():
    cc = load_check_claims()
    claims, private = cc.actual()
    if private:
        sys.exit(f"error: private theorems in Plonky3Lean.Claims: {private}")
    cs = crates()
    lib_of = {c["lean_lib"]: name for name, c in cs}
    mirrors = [(name, m) for name, c in cs for m in c.get("mirror", [])]
    facts = lean_facts(list(lib_of), list(claims), sorted({m["lean"] for _, m in mirrors}))
    opaques = sorted((f for f in facts if f["kind"] == "opaque"), key=lambda f: (f["module"], f["name"]))
    mreach = {f["name"]: f for f in facts if f["kind"] == "mirror"}
    for name, m in mirrors:
        if not mreach[m["lean"]]["exists"]:
            sys.exit(f"error: crates/{name}/crate.toml mirrors `{m['lean']}`, which is not declared")

    def crate_of(module):
        return next((lib_of[l] for l in lib_of if module.startswith(l)), "?")

    tc = tomllib.loads((ROOT / "toolchain.toml").read_text())["extractor"]
    # The gitlink in the tree, so that a checkout without submodules (CI) works.
    pin = sh("git", "rev-parse", "HEAD:plonky3")
    n = len(claims)
    out = []
    w = out.append

    w("# Status\n")
    w("Generated by `tools/status.py` from the pinned commit, `toolchain.toml`,")
    w("`crates/*/crate.toml`, the crates' Lean files and extraction reports")
    w("(`crates/*/extraction/gaps.toml`), the patch headers, `claims.toml` and the Lean")
    w("build. Do not edit by hand: run `tools/status.py`. CI fails if it is out of date.\n")
    w(f"**Plonky3:** [`{pin[:8]}`](https://github.com/Plonky3/Plonky3/commit/{pin})\n")
    w(f"**Extractor:** hax {tc['hax_version']} (charon `{tc['charon']}`, aeneas `{tc['aeneas']}`),")
    w(f"target `{tc['target']}`\n")

    # Crates
    w("## Crates\n")
    w("| Crate | State | Generated lines | Hand-written lines | `opaque` | Mirrored | Dropped by the extractor | Patches (pre / post) | Patches with a cost |")
    w("|---|---|---:|---:|---:|---:|---:|---|---|")
    costed = []
    for name, c in cs:
        gen, hand = lean_files(name, c)
        ps = patches(name)
        pre = sum(1 for p in ps if p[0] == "pre")
        cost = [p for p in ps if has_cost(p[2].get("Cost", ""))]
        costed += [(name, p) for p in cost]
        g = gaps(name)
        dropped = "" if g is None else str(len(g.get("dropped", [])))
        n_op = sum(1 for o in opaques if crate_of(o["module"]) == name)
        n_mir = len(c.get("mirror", []))
        w(f"| `{name}` | {c['state']} | {lines(gen) if gen else ''} | {lines(hand)} | {n_op} | "
          f"{n_mir} | {dropped} | {pre} / {len(ps) - pre} | "
          + ", ".join(f"{p[0]} `{p[1].name[:3]}`" for p in cost) + " |")
    w("")
    w("Generated lines are `extraction/<Lib>/Extraction/{Types,Funs}.lean`. Hand-written")
    w("lines are every other `.lean` file of the crate. *Dropped by the extractor* counts")
    w("the items of the crate that charon translated with a body and aeneas did not emit")
    w("(`docs/extractor-issues.md`, 4); the extraction gaps below list them. The")
    w("`[[mirror]]` entries have no hashes yet (`tools/mirror` is planned).\n")

    # Extraction gaps
    w("## Extraction gaps\n")
    w("From each extracted crate's `extraction/gaps.toml`, which `extract.sh` writes from")
    w("charon's output and `--check` requires to reproduce. An item is *mirrored* when a")
    w("`[[mirror]]` entry transcribes it by hand.\n")
    mkeys = {mirror_key(m["rust"]): m for _, m in mirrors}
    for name, c in cs:
        g = gaps(name)
        if g is None:
            continue
        ch = g["charon"]
        sites = ", ".join(f"`{s}`" for s in ch.get("error_sites", []))
        w(f"### `{name}`\n")
        w(f"charon errors: {ch['errors']}" + (f", at {sites}." if sites else "."))
        dr = g.get("dropped", [])
        if not dr:
            w("Nothing translated is dropped.\n")
            continue
        w(f"{len(dr)} item(s) dropped, {sum(1 for d in dr if d['item'] in mkeys)} of them mirrored.\n")
        w("| Item | Source | Mirrored |")
        w("|---|---|---|")
        for d in dr:
            w(f"| `{d['item']}` | `{d['source']}` | {'yes' if d['item'] in mkeys else ''} |")
        w("")

    # Assumptions
    w("## Assumptions\n")
    w("Every `opaque` constant, all hand-written. An opaque constant is not an axiom: it")
    w("adds nothing to a claim's axioms, and Lean cannot unfold it, so a proof about code")
    w("that mentions one would go through for any value of it. *Claims* counts the claims")
    w(f"(of {n}) whose dependencies include it; reaching one is not using it.\n")
    w("| Crate | Constant | Why | Claims |")
    w("|---|---|---|---:|")
    for o in opaques:
        w(f"| `{crate_of(o['module'])}` | `{o['name']}` | {assumed(o['doc'], o['name'])} | {o['reach']} |")
    w("")

    # Transcriptions
    w("## Transcriptions\n")
    w("Every `[[mirror]]` entry: a hand-written Lean declaration that transcribes a Rust")
    w("item, re-read by hand when upstream changes it until `tools/mirror` hashes the Rust")
    w("item. *Extractor* says what the last extraction did with the Rust item: dropped")
    w("after translating it, or not translated (a stub's item, or not reached). *Claims*")
    w(f"counts the claims (of {n}) whose dependencies include the declaration.\n")
    w("| Crate | Lean | Rust | Extractor | Claims |")
    w("|---|---|---|---|---:|")
    dropped_items = {d["item"] for name, c in cs for d in (gaps(name) or {}).get("dropped", [])}
    for name, m in mirrors:
        k = mirror_key(m["rust"])
        ex = ("stub" if dict(cs)[name]["state"] == "stub"
              else "dropped" if k in dropped_items else "not translated")
        w(f"| `{name}` | `{m['lean']}` | `{m['rust']}` | {ex} | {mreach[m['lean']]['reach']} |")
    w("")

    # Patches
    w("## Patches with a cost\n")
    w("| Patch | Cost |")
    w("|---|---|")
    for name, (phase, pf, h) in costed:
        w(f"| `{name}/{phase}/{pf.stem}` | {h['Cost']} |")
    w("")
    runs = [h["Tested"] for name, _ in cs for ph, _, h in patches(name)
            if ph == "pre" and "Tested" in h]
    if runs:
        m = re.search(r"(\d+) of (\d+) upstream tests pass as\s+shipped, (\d+) with", runs[0])
        div = sum(int(x) for t in runs for x in re.findall(r"(\d+) divergences?", t))
        if m:
            w(f"Upstream tests (`test-pre-patches.py`): {m.group(1)} of Plonky3's {m.group(2)} "
              f"pass as shipped and {m.group(3)} with the pre-extraction patches, with "
              f"{div} divergence(s).\n")

    # Claims
    w("## Claims\n")
    w("Every theorem in `Plonky3Lean.Claims`, without the `Plonky3Lean.Claims.` prefix.")
    w("`tools/check-claims.py` checks each one's axioms against `claims.toml`.\n")
    w("| Claim | Axioms |")
    w("|---|---|")
    for cl, axs in sorted(claims.items()):
        w(f"| `{cl.removeprefix(CLAIMS_PREFIX)}` | " + ", ".join(f"`{a}`" for a in axs) + " |")
    w("")

    w("## Upstream warnings\n")
    w("Warnings from pinned dependencies, not from this repository. CI allows exactly these.\n")
    w("\n".join(f"- {x}" for x in UPSTREAM_WARNINGS) if UPSTREAM_WARNINGS else "None.")
    return "\n".join(out) + "\n"


def main(argv):
    if argv not in ([], ["--check"]):
        sys.exit(__doc__)
    text = generate()
    target = ROOT / "STATUS.md"
    if argv == ["--check"]:
        if target.read_text() != text:
            sys.exit("error: STATUS.md is out of date; run tools/status.py and commit the result")
        print("status: STATUS.md is up to date")
        return
    target.write_text(text)
    print("status: wrote STATUS.md")


if __name__ == "__main__":
    main(sys.argv[1:])
