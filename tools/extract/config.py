#!/usr/bin/env python3
"""config.py -- read toolchain.toml and crates/*/crate.toml for the shell tools.

  config.py toolchain <key>     a value from toolchain.toml's [extractor]
  config.py crates              one line per crate: <dir>|<lean_lib>|<state>
  config.py charon-args <dir>   the --charon-args string for one crate
  config.py rustflags <dir>     the RUSTFLAGS of one crate's extraction
  config.py package <dir>       the Cargo package one crate directory models
  config.py source <dir>        that package's source directory
  config.py pre-patches         every crates/*/patches/pre/*.patch, in apply order
"""
import json
import shlex
import subprocess
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


def package(name, c):
    """A workspace crate is `p3-<dir>`; a dependency names its package."""
    return c.get("package", f"p3-{name}")


def source(name, c):
    """A workspace crate's directory, or the one Cargo resolves the dependency to."""
    if "package" not in c:
        return ROOT / "plonky3" / name
    meta = json.loads(subprocess.run(
        ["cargo", "metadata", "--format-version", "1", "--filter-platform",
         toolchain()["target"]],
        cwd=ROOT / "plonky3", check=True, capture_output=True, text=True).stdout)
    # The version a workspace crate depends on, not one deeper in the graph.
    members = set(meta["workspace_members"])
    direct = {d["pkg"] for n in meta["resolve"]["nodes"] if n["id"] in members
              for d in n["deps"]}
    found = [Path(p["manifest_path"]).parent for p in meta["packages"]
             if p["name"] == c["package"] and p["id"] in direct]
    if len(found) != 1:
        sys.exit(f"error: Cargo resolves {len(found)} packages named {c['package']}")
    return found[0]


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
        args += c.get("charon_args", [])
        print(" ".join(shlex.quote(a) for a in args))
    elif argv[:1] == ["rustflags"] and len(argv) == 2:
        c = dict(crates())[argv[1]]
        print(" ".join([toolchain()["rustflags"], *c.get("rustflags", [])]))
    elif argv[:1] == ["package"] and len(argv) == 2:
        print(package(argv[1], dict(crates())[argv[1]]))
    elif argv[:1] == ["source"] and len(argv) == 2:
        print(source(argv[1], dict(crates())[argv[1]]))
    elif argv == ["pre-patches"]:
        # Crate by crate, each crate's patches in filename order. Every
        # extraction run applies all of them: the cfg they gate on is set for
        # every crate, so the trees the crates see must agree.
        # A `NNN-slug.mutation.patch` is the recorded mutation of patch
        # NNN-slug (check-mutations.py), not a patch.
        for name, _ in crates():
            for p in sorted((ROOT / "crates" / name / "patches" / "pre").glob("[0-9]*.patch")):
                if not p.name.endswith(".mutation.patch"):
                    print(p)
    else:
        sys.exit(__doc__)


if __name__ == "__main__":
    main(sys.argv[1:])
