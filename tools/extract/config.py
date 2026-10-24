#!/usr/bin/env python3
"""config.py -- read toolchain.toml and crates/*/crate.toml for the shell tools.

  config.py toolchain <key>     a value from toolchain.toml's [extractor]
  config.py crates              one line per crate: <dir>|<lean_lib>|<state>
  config.py units               one line per extraction unit, every crate and
                                then every variant:
                                <unit>|<lean_lib>|<state>|<home>
  config.py charon-args <unit>  the --charon-args string for one unit
  config.py rustflags <unit>    the RUSTFLAGS of one unit's extraction
  config.py target <unit>       the target triple charon compiles the unit for
  config.py features <unit>     the Cargo features of one unit's extraction, comma-separated
  config.py package <unit>      the Cargo package one unit models
  config.py source <unit>       that package's source directory
  config.py rename <unit>       for a variant, `<lib> <namespace> <new lib>
                                <new namespace>`: hax's names and the variant's
  config.py checks              the `cargo check`s of the pre-patched tree, one
                                line per target: <target>|<rustflags>|<-p args>
  config.py pre-patches         every crates/*/patches/pre/*.patch, in apply order

A unit is a crate directory (`monty-31`) or one of its `[[variant]]` tables
(`monty-31@x86_64-avx2`): the same package extracted for another target, with
its own roots, into crates/<dir>/variants/<name>/ (docs/extracting.md). Its
`<home>` is the directory holding its `extraction/` and `patches/post/`.
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


def variants():
    """[(unit, crate dir, crate table, variant table)] for every `[[variant]]`."""
    out = []
    for name, c in crates():
        for v in c.get("variant", []):
            for k in ("name", "target", "lean_lib", "namespace", "start_from"):
                if k not in v:
                    sys.exit(f"error: crates/{name}/crate.toml: a [[variant]] has no `{k}`")
            out.append((f"{name}@{v['name']}", name, c, v))
    return out


def unit(u):
    """(crate dir, crate table, variant table or None) of a unit name."""
    name, _, var = u.partition("@")
    c = dict(crates())[name]
    if not var:
        return name, c, None
    vs = [v for v in c.get("variant", []) if v["name"] == var]
    if len(vs) != 1:
        sys.exit(f"error: crates/{name}/crate.toml has no [[variant]] named {var}")
    return name, c, vs[0]


def namespace(name, c):
    """The namespace hax gives a crate's items: its package name, `-` as `_`."""
    return package(name, c).replace("-", "_")


def package(name, c):
    """A workspace crate is `p3-<dir>`; a dependency names its package."""
    return c.get("package", f"p3-{name}")


def source(name, c):
    """A workspace crate's directory, a crate of this repository's (`path`), or
    the one Cargo resolves the dependency to."""
    if "path" in c:
        return ROOT / c["path"]
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
    elif argv == ["units"]:
        for name, c in crates():
            print(f"{name}|{c['lean_lib']}|{c['state']}|crates/{name}")
        for u, name, c, v in variants():
            print(f"{u}|{v['lean_lib']}|scoped|crates/{name}/variants/{v['name']}")
    elif argv[:1] == ["charon-args"] and len(argv) == 2:
        name, c, v = unit(argv[1])
        if v is None:
            args = ["--targets", toolchain()["target"], *toolchain()["charon_args"], *c.get("charon_args", [])]
            for root in c.get("start_from", []):
                args += ["--start-from", root]
            args += c.get("charon_args", [])
        else:
            # A variant's own roots; its `opaque` modules are the crate's
            # portable code, which the variant takes from the crate's library.
            args = ["--targets", v["target"], *toolchain()["charon_args"]]
            for root in v["start_from"]:
                args += ["--start-from", root]
            for item in v.get("opaque", []):
                args += ["--opaque", item]
            args += v.get("charon_args", [])
        print(" ".join(shlex.quote(a) for a in args))
    elif argv[:1] == ["rustflags"] and len(argv) == 2:
        name, c, v = unit(argv[1])
        flags = [toolchain()["rustflags"], *c.get("rustflags", [])]
        if v is not None:
            flags += [f"-Ctarget-feature=+{f}" for f in v.get("target_features", [])]
        print(" ".join(flags))
    elif argv[:1] == ["features"] and len(argv) == 2:
        name, c, _ = unit(argv[1])
        print(",".join(c.get("features", [])))
    elif argv[:1] == ["target"] and len(argv) == 2:
        name, c, v = unit(argv[1])
        print(toolchain()["target"] if v is None else v["target"])
    elif argv[:1] == ["rename"] and len(argv) == 2:
        name, c, v = unit(argv[1])
        if v is None:
            sys.exit(f"error: {argv[1]} is a crate, not a variant")
        print(c["lean_lib"], namespace(name, c), v["lean_lib"], v["namespace"])
    elif argv == ["checks"]:
        # The crates in plonky3/'s dependency graph, as charon sees them: the
        # crates for the extraction target, and each variant for its own. A
        # `path` crate is checked by its own build, and is not a package of
        # the unpatched tree.
        groups = {}
        base = (toolchain()["target"], toolchain()["rustflags"])
        for name, c in crates():
            if c["state"] != "stub" and "path" not in c:
                groups.setdefault(base, []).append(package(name, c))
        for u, name, c, v in variants():
            flags = " ".join([toolchain()["rustflags"],
                              *(f"-Ctarget-feature=+{f}" for f in v.get("target_features", []))])
            groups.setdefault((v["target"], flags), []).append(package(name, c))
        for (target, flags), pkgs in groups.items():
            print(f"{target}|{flags}|" + " ".join(f"-p {p}" for p in dict.fromkeys(pkgs)))
    elif argv[:1] == ["package"] and len(argv) == 2:
        name, c, _ = unit(argv[1])
        print(package(name, c))
    elif argv[:1] == ["source"] and len(argv) == 2:
        name, c, _ = unit(argv[1])
        print(source(name, c))
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
