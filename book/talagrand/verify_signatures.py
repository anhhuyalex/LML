#!/usr/bin/env python3
"""Check that every Lean name cited by the chapter has a signature in ``lean.json``.

``tex2typ`` writes ``generated/lean-names.json`` (all ``\\lean{...}`` names); the book build
then asks Lean to ``#check`` each of them. This script reports names whose result is missing
or is an error message, so that a renamed or private declaration is noticed at build time.

Usage: verify_signatures.py generated/lean-names.json ../typstverso/typst/lean.json
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path

CHECK = re.compile(r"#check\s+(\S+)\s*$")


def checked_results(lean_json: dict) -> dict[str, list[str]]:
    """Map each ``#check``-ed name to the severities of Lean's messages for it."""
    results: dict[str, list[str]] = {}
    for command in lean_json.get("inlineCommands", []):
        match = CHECK.search(command["source"].strip())
        if match:
            results[match.group(1)] = [m.get("severity", "info") for m in command["messages"]]
    return results


def problems(names: list[str], lean_json: dict) -> dict[str, str]:
    """Names that are missing, have no message, or produced an error: name -> reason."""
    results = checked_results(lean_json)
    found: dict[str, str] = {}
    for name in names:
        if name not in results:
            found[name] = "no #check result (run the book build to extract it)"
        elif not results[name]:
            found[name] = "Lean printed nothing"
        elif "error" in results[name]:
            found[name] = "Lean reported an error (renamed, private or ambiguous?)"
    return found


def main(argv: list[str]) -> int:
    if len(argv) != 3:
        print(__doc__, file=sys.stderr)
        return 2
    names = json.loads(Path(argv[1]).read_text(encoding="utf-8"))
    lean_json = json.loads(Path(argv[2]).read_text(encoding="utf-8"))
    found = problems(names, lean_json)
    for name, reason in sorted(found.items()):
        print(f"{name}: {reason}")
    print(f"{len(names) - len(found)} of {len(names)} Lean names have a signature.")
    return 1 if found else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
