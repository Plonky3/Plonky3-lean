#!/usr/bin/env python3
"""config.py -- read toolchain.toml and crates/*/crate.toml for the shell tools.

  config.py toolchain <key>     a value from toolchain.toml's [extractor]
  config.py crates              one line per crate: <dir>|<lean_lib>|<state>
  config.py charon-args <dir>   the --charon-args string for one crate
  config.py pre-patches         every crates/*/patches/pre/*.patch, in apply order
"""
import shlex
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
STATES = {"extracted", "scoped", "stub"}


def toolchain():
    return tomllib.loads((ROOT / "toolchain.toml").read_text())["extractor"]


def crates():
    out = []
    for d in sorted((ROOT / "crates").iterdir()):
        f = d / "crate.toml"
        if d.name.startswith("_") or not f.is_file():
            continue
        c = tomllib.loads(f.read_text())
        if c.get("state") not in STATES:
            sys.exit(f"error: {f}: state must be one of {sorted(STATES)}")
        out.append((d.name, c))
    return out


def main(argv):
    if argv[:1] == ["toolchain"] and len(argv) == 2:
        v = toolchain()[argv[1]]
        print(" ".join(v) if isinstance(v, list) else v)
    elif argv == ["crates"]:
        for name, c in crates():
            print(f"{name}|{c['lean_lib']}|{c['state']}")
    elif argv[:1] == ["charon-args"] and len(argv) == 2:
        c = dict(crates())[argv[1]]
        args = ["--targets", toolchain()["target"], *toolchain()["charon_args"]]
        for root in c.get("start_from", []):
            args += ["--start-from", root]
        print(" ".join(shlex.quote(a) for a in args))
    elif argv == ["pre-patches"]:
        # Crate by crate, each crate's patches in filename order. Every
        # extraction run applies all of them: the cfg they gate on is set for
        # every crate, so the trees the crates see must agree.
        for name, _ in crates():
            for p in sorted((ROOT / "crates" / name / "patches" / "pre").glob("[0-9]*.patch")):
                print(p)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
