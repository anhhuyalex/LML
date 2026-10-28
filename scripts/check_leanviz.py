#!/usr/bin/env python3
"""Validate LML's bundle and exercise the assembled site under its /leanviz/ prefix."""
from __future__ import annotations

import functools
import gzip
import http.server
import json
import pathlib
import subprocess
import sys
import threading
import time
import urllib.parse


def read_json(path: pathlib.Path):
    if path.exists():
        return json.loads(path.read_text())
    return json.loads(gzip.decompress(path.with_suffix(path.suffix + ".gz").read_bytes()))


def require(condition, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def main(tools: pathlib.Path, repository: str) -> None:
    project = pathlib.Path(__file__).resolve().parent.parent
    site = project / "home_page" / "leanviz"
    bundle = site / "data" / "lml"
    manifest = read_json(bundle / "manifest.json")
    expected_lean = (project / "lean-toolchain").read_text().strip().split(":v")[-1]
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=project, text=True).strip()
    require(manifest["lean"] == expected_lean, "Bundle uses the wrong Lean version")
    require(manifest["slug"] == "lml", "Bundle has the wrong slug")
    require(manifest["repository"] == repository, "Bundle has the wrong repository")
    require(manifest["check"] is None, "Visualization must not claim an independent proof check")
    own = set(manifest["ownModules"])
    require("LeanMachineLearning" in own, "Bundle is missing the root LML module")
    modules = read_json(bundle / "modules.json")
    own_modules = [m for m in modules if m["n"] in own and m["n"].startswith("LeanMachineLearning.")]
    require(own_modules, "Bundle contains no LML submodules")
    library = next(lib for lib in manifest["libraries"] if not lib["prefixes"])
    require(library["url"] == repository and library["rev"] == revision,
            "Project source links must use this repository and checkout revision")
    require(read_json(site / "data" / "projects.json")[0]["slug"] == "lml",
            "The default project must be LML")

    # Upstream checks sample early dependency shards. Inspect every project shard as well,
    # and choose a public theorem with dependencies and source lines for the browser check.
    sample = None
    for module in own_modules:
        declarations = read_json(bundle / "m" / (module["n"] + ".json"))
        require(len(declarations) == module["c"], f"Incomplete shard: {module['n']}")
        for declaration in declarations:
            require(bool(declaration.get("s")), f"Missing statement: {declaration['n']}")
            if (sample is None and declaration["k"] == "theorem" and declaration.get("l")
                    and (declaration["t"] or declaration["u"])
                    and not declaration["n"].startswith("_")
                    and all(c.isalnum() or c in "_.'" for c in declaration["n"])):
                sample = module["n"], declaration
    require(sample is not None, "No LML theorem with source lines and dependencies found")
    module_name, declaration = sample
    print(f"Validated LML metadata and {len(own_modules)} project shards; Lean {expected_lean}", flush=True)

    sys.path.insert(0, str(tools / "tests"))
    from check_page import Page

    class QuietHandler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *args):
            pass

    handler = functools.partial(QuietHandler, directory=str(site.parent))
    with http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler) as server:
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        base = f"http://127.0.0.1:{server.server_port}/leanviz"
        try:
            for check in ("check_page.py", "check_ui.py"):
                subprocess.run([sys.executable, str(tools / "tests" / check), base], check=True)
            page = Page()
            try:
                page.visit(base + "/?p=lml#/", "!!document.querySelector('#q') && !!document.querySelector('.tab')")
                name = declaration["n"]
                encoded_name = json.dumps(name)
                page.value(f"""(() => {{
                    const scope = document.querySelector('#scope');
                    if (!scope.checked) {{ scope.checked = true; scope.dispatchEvent(new Event('change')); }}
                    const query = document.querySelector('#q');
                    query.value = {encoded_name}; query.dispatchEvent(new Event('input'));
                }})()""")
                result = f"[...document.querySelectorAll('#results a')].find(a => a.querySelector('.nm')?.textContent === {encoded_name})"
                deadline = time.monotonic() + 60
                while not page.value(f"!!({result})"):
                    require(time.monotonic() < deadline, f"Search did not find {name}")
                    time.sleep(0.25)
                page.value(f"({result}).click()")
                route = urllib.parse.quote(name, safe="")
                # Assert the search result navigated to the expected declaration before reloading its deep link.
                require(page.value("location.hash") == f"#/i/{declaration['i']}", "Search opened the wrong declaration")
                page.visit(base + f"/?p=lml#/d/{route}", "document.querySelectorAll('#graph svg a').length > 1")
                require(page.value("document.querySelector('h1').textContent") == name,
                        "Declaration page has the wrong title")
                require(page.value("!!document.querySelector('.theorem, pre')"), "Statement did not render")
                expected_source = (f"{repository}/blob/{revision}/{module_name.replace('.', '/')}.lean"
                                   f"#L{declaration['l'][0]}-L{declaration['l'][1]}")
                sources = page.value("[...document.querySelectorAll('#main p.sub a')].map(a => a.href)")
                require(expected_source in sources, "Declaration source link has the wrong repository, revision or lines")
                require("Not re-checked" in page.value("document.querySelector('#foot').textContent"),
                        "Footer must disclose that independent checking was not run")
                problems = page.problems()
                require(not problems, f"Browser reported errors on the LML declaration: {problems}")
                print(f"LML search, statement, dependency graph and source link passed: {name}", flush=True)
            finally:
                page.close()
        finally:
            server.shutdown()
            thread.join()


if __name__ == "__main__":
    main(pathlib.Path(sys.argv[1]).resolve(), sys.argv[2])
