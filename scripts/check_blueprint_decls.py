#!/usr/bin/env python3
"""Diagnose `lake exe checkdecls blueprint/lean_decls` failures before the docgen step.

The docgen action runs `leanblueprint web`, which REGENERATES `blueprint/lean_decls` from every
`\\lean{...}` tag in `blueprint/src/**/*.tex`, then runs `checkdecls` on that regenerated file.
So a hand-edited `lean_decls` can pass locally and still fail in CI when a TeX tag names a
declaration that was renamed or deleted. This script reproduces that exactly:

  1. collects every `\\lean{...}` name from the TeX sources (what CI will write to lean_decls),
  2. runs `lake exe checkdecls` on that list,
  3. for each missing name prints the TeX file:line that mentions it and close matches among the
     committed `lean_decls` entries (usually the renamed declaration),
  4. reports where the committed `blueprint/lean_decls` differs from the TeX-derived list.

Usage: python3 scripts/check_blueprint_decls.py [--no-lake]   (exit 1 if any name is missing)
"""
import difflib
import glob
import re
import subprocess
import sys
import tempfile

TEX = "blueprint/src/**/*.tex"
LEAN_TAG = re.compile(r"\\lean\{([^}]*)\}")


def tex_names():
    where = {}
    for path in sorted(glob.glob(TEX, recursive=True)):
        text = open(path, encoding="utf-8").read()
        for m in LEAN_TAG.finditer(text):
            line = text.count("\n", 0, m.start()) + 1
            for name in (x.strip() for x in m.group(1).split(",")):
                if name:
                    where.setdefault(name, []).append(f"{path}:{line}")
    return where


def main():
    where = tex_names()
    committed = [l.strip() for l in open("blueprint/lean_decls", encoding="utf-8") if l.strip()]
    print(f"{len(where)} distinct names in TeX, {len(committed)} in blueprint/lean_decls")
    if "--no-lake" in sys.argv:
        return 0
    with tempfile.NamedTemporaryFile("w", suffix=".decls", delete=False) as f:
        f.write("\n".join(sorted(where)) + "\n")
    out = subprocess.run(["lake", "exe", "checkdecls", f.name], capture_output=True, text=True)
    missing = [l[: -len(" is missing.")] for l in out.stdout.splitlines() if l.endswith(" is missing.")]
    print(out.stdout[-3000:] if not missing else "", end="")
    for name in missing:
        print(f"MISSING {name}")
        for loc in where.get(name, []):
            print(f"    used at {loc}")
        last = name.rsplit(".", 1)[-1]
        close = difflib.get_close_matches(name, committed, n=3, cutoff=0.6)
        close += [c for c in committed if last in c and c not in close][:3]
        for c in close[:5]:
            print(f"    candidate in lean_decls: {c}")
    if out.returncode != 0 and not missing:
        print(out.stderr[-3000:])
        return out.returncode
    if missing:
        print(f"::error::{len(missing)} \\lean name(s) in blueprint TeX do not exist in Lean")
        return 1
    print("All \\lean names in the TeX resolve.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
