#!/usr/bin/env python3
"""default-features.py <Cargo.toml> <f1,f2,...> -- make those the manifest's default features.

Runs on extract.sh's copy of a crate outside the workspace, never on a source
Cargo resolves to: hax's lean backend does not pass cargo arguments on to
charon, so the default features are the only way to select them
(docs/extractor-issues.md 90).
"""
import re
import sys
import tomllib

path, feats = sys.argv[1], sys.argv[2].split(",")
text = open(path).read()
known = tomllib.loads(text).get("features", {})
missing = [f for f in feats if f not in known]
if missing:
    sys.exit(f"error: {path} has no feature {', '.join(missing)}")
line = "default = [" + ", ".join(f'"{f}"' for f in feats) + "]"
# The `default` key of the `[features]` table, which a published manifest writes on one line.
section = re.search(r"^\[features\]\n(?:(?!^\[).*\n?)*", text, re.M)
if section and re.search(r"^default\s*=.*$", section.group(0), re.M):
    body = re.sub(r"^default\s*=.*$", line, section.group(0), count=1, flags=re.M)
elif section:
    body = section.group(0).replace("[features]\n", "[features]\n" + line + "\n", 1)
else:
    text += "\n[features]\n" + line + "\n"
    body = None
if body is not None:
    text = text[: section.start()] + body + text[section.end():]
assert tomllib.loads(text)["features"]["default"] == feats
open(path, "w").write(text)
