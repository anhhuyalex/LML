#!/usr/bin/env python3
"""Add Stats to an already rendered exposition using the Referee action's data output."""
from __future__ import annotations

import argparse
import hashlib
import json
import pathlib
import subprocess

from website_stats.metrics import results
from website_stats.reader import REFEREE_COMMIT, REFEREE_VERSION, catalog, decode
from website_stats.render import build_site


def build(data_path, site, project, repository, revision):
    raw = data_path.read_bytes()
    data = decode(json.loads(raw))
    declarations, excluded = catalog(data, site, project, repository, revision)
    bundle = {"schema_version": 1,
              "build": {"repository": repository, "revision": revision,
                        "lean": (project / "lean-toolchain").read_text().strip(),
                        "referee_commit": REFEREE_COMMIT, "referee_release": REFEREE_VERSION,
                        "input_sha256": hashlib.sha256(raw).hexdigest()},
              "population": {"description": "Named public declarations authored in LML",
                             "collected": len(data["decls"]), "included": len(declarations),
                             "excluded": excluded},
              "declarations": declarations, "metrics": results(declarations, data)}
    pages = build_site(site, bundle)
    print(f"Stats: {len(declarations)} declarations; exclusions {excluded}; {pages} pages updated")
    return bundle


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--data", required=True, type=pathlib.Path)
    parser.add_argument("--site", type=pathlib.Path, default=pathlib.Path("home_page/exposition"))
    parser.add_argument("--project", type=pathlib.Path, default=pathlib.Path.cwd())
    parser.add_argument("--repository", required=True)
    args = parser.parse_args()
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=args.project, text=True).strip()
    try:
        build(args.data, args.site, args.project, args.repository.rstrip("/"), revision)
    except (ValueError, KeyError, TypeError) as error:
        parser.exit(1, f"Stats build failed: {error}\n")
