#!/usr/bin/env python3
"""check-claims.py -- check the axioms of every claim against claims.toml.

Lists every theorem in `Plonky3Lean.Claims` with the axioms it depends on (what
`#print axioms` reports) and requires the result to equal claims.toml exactly:
every claim has an entry, every entry names a claim, and each claim's axioms are
the ones its entry allows. A claim that starts to depend on `sorryAx`, or on the
`Lean.ofReduceBool` axiom that `native_decide` adds, therefore fails.

Run after `lake build`.

  tools/check-claims.py           check
  tools/check-claims.py --print   print the claims and their axioms as
                                  claims.toml entries, and check nothing
"""
import subprocess
import sys
import tempfile
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

LIST_CLAIMS = """\
import Plonky3Lean
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let claims := env.constants.toList.filter fun (n, ci) =>
    (`Plonky3Lean.Claims).isPrefixOf n && !n.isInternal && ci matches .thmInfo _
  for (n, _) in claims.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let axs ← liftCoreM (Lean.collectAxioms n)
    let axs := axs.qsort (fun a b => a.toString < b.toString)
    IO.println s!"{n}\\t{String.intercalate "," (axs.toList.map toString)}"
"""


def actual():
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(LIST_CLAIMS)
    try:
        r = subprocess.run(["lake", "env", "lean", f.name], cwd=ROOT, text=True,
                           capture_output=True)
    finally:
        Path(f.name).unlink()
    if r.returncode != 0:
        sys.exit(f"error: listing the claims failed (run `lake build` first?):\n{r.stdout}{r.stderr}")
    out = {}
    for line in r.stdout.splitlines():
        name, _, axs = line.partition("\t")
        out[name] = sorted(a for a in axs.split(",") if a)
    return out


def main(argv):
    claims = actual()
    if argv == ["--print"]:
        for name, axs in claims.items():
            print("[[claim]]")
            print(f'name   = "{name}"')
            print("axioms = [" + ", ".join(f'"{a}"' for a in axs) + "]")
            print()
        return
    if argv:
        sys.exit(__doc__)
    allowed = {c["name"]: sorted(c["axioms"])
               for c in tomllib.loads((ROOT / "claims.toml").read_text()).get("claim", [])}
    fail = False
    for name, axs in claims.items():
        if name not in allowed:
            print(f"FAIL: {name} is a claim with no claims.toml entry (axioms: {axs})")
            fail = True
        elif axs != allowed[name]:
            print(f"FAIL: {name} depends on {axs}; claims.toml allows {allowed[name]}")
            fail = True
    for name in allowed:
        if name not in claims:
            print(f"FAIL: claims.toml names {name}, which is not a theorem in Plonky3Lean.Claims")
            fail = True
    if fail:
        sys.exit(1)
    print(f"check-claims: {len(claims)} claim(s), each with exactly the axioms claims.toml allows")


if __name__ == "__main__":
    main(sys.argv[1:])
