#!/usr/bin/env python3
"""rename-variant.py -- give a variant's hax output its own library and namespace.

hax names a crate's Lean library and namespace after the package (`P3Monty31`,
`p3_monty_31`), whatever the target, so a variant's output would collide with
the crate's own. This renames, in place, in the output directory of one run:

  - the module root: `<lib>/` and `<lib>.lean` become `<new lib>/` and
    `<new lib>.lean`, and every `import <lib>.` becomes `import <new lib>.`;
  - the namespace: the `namespace <ns>`, `end <ns>` and `open <ns>` lines
    become `<new ns>`;
  - each of the variant's `renames`, `<from>=<to>`: every absolute reference
    `<from>.` to another crate's item becomes `<to>.`, for a crate whose items
    this target takes from a variant of it (`p3_monty_31.` to
    `p3_monty_31_avx2.`, when the AVX2 trait declarations live there).

The generated code refers to its own crate's items by names relative to the
namespace, and to other crates' items by absolute names, so nothing else
changes. A variant that keeps the crate's namespace (`<ns>` = `<new ns>`)
renames the module root only.

  rename-variant.py <out dir> <lib> <ns> <new lib> <new ns> [<from>=<to> ...]
"""
import re
import sys
from pathlib import Path


def main(argv):
    if len(argv) < 5:
        sys.exit(__doc__)
    out, lib, ns, new_lib, new_ns = Path(argv[0]), *argv[1:5]
    renames = []
    for arg in argv[5:]:
        old, sep, new = arg.partition("=")
        if not sep or not old or not new:
            sys.exit(f"error: a rename is `<from>=<to>`, not `{arg}`")
        # An absolute reference: `<from>.` not preceded by part of a longer
        # name, so `p3_monty_31.` matches but `p3_monty_31_avx2.` and
        # `x.p3_monty_31.` do not.
        renames.append((re.compile(rf"(?<![\w.]){re.escape(old)}\."), f"{new}."))
    if not (out / lib).is_dir():
        sys.exit(f"error: {out / lib} does not exist")
    if (out / new_lib).exists():
        sys.exit(f"error: {out / new_lib} already exists")
    (out / lib).rename(out / new_lib)
    if (out / f"{lib}.lean").exists():
        (out / f"{lib}.lean").rename(out / f"{new_lib}.lean")
    imp = re.compile(rf"^((?:public )?import ){re.escape(lib)}(\.|$)", re.M)
    scope = re.compile(rf"^(namespace|end|open) {re.escape(ns)}$", re.M)
    for f in sorted([out / f"{new_lib}.lean", *(out / new_lib).rglob("*.lean")]):
        if not f.is_file():
            continue
        s = f.read_text()
        t = imp.sub(rf"\g<1>{new_lib}\g<2>", s)
        t = scope.sub(rf"\g<1> {new_ns}", t)
        for pat, repl in renames:
            t = pat.sub(repl, t)
        if t != s:
            f.write_text(t)


if __name__ == "__main__":
    main(sys.argv[1:])
