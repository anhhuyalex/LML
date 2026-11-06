#!/usr/bin/env python3
"""Validate Stats counts, local links, navigation and real browser interactions.

With no arguments, builds and tests a small example (for PRs). Pass --site for a full site.
"""
from __future__ import annotations

import argparse
import functools
import http.server
import json
import pathlib
import subprocess
import sys
import tempfile
import threading
import time

from build_stats import build
from website_stats.browser import Page
from website_stats.example import REPOSITORY, REVISION, make_fixture
from website_stats.reader import local_target, require
from website_stats.render import PageParts


def validate(site):
    bundle = json.loads((site / "stats/data.json").read_text())
    require(bundle["schema_version"] == 1, "Unknown statistics format")
    declarations = bundle["declarations"]
    names = {d["id"] for d in declarations}
    require(len(names) == len(declarations) == bundle["population"]["included"],
            "Invalid declaration population")
    require(len(names) + sum(bundle["population"]["excluded"].values()) ==
            bundle["population"]["collected"], "Population counts do not add up")
    for metric in bundle["metrics"]:
        require(set(metric["values"]) == names, f"Incomplete metric: {metric['id']}")
        require(all(type(value) is int and value >= 0
                    for value in metric["values"].values()), "Invalid reuse counts")
        if metric["id"] == "reuse":
            require(all(value < len(names) for value in metric["values"].values()),
                    "A reuse count exceeds the number of other declarations")
    for declaration in declarations:
        local_target(site, declaration["documentation"])
        expected = (f"{bundle['build']['repository']}/blob/{bundle['build']['revision']}/"
                    f"{declaration['file']}#L{declaration['line']}-L{declaration['end_line']}")
        require(declaration["source"] == expected, "Incorrect source repository, commit or lines")
    pages = 0
    for path in site.rglob("*.html"):
        parts = PageParts(path.read_text())
        if parts.has_toc:
            require(len(parts.sorries) == 1 and len(parts.stats) == 1,
                    f"Stats navigation missing or duplicated: {path}")
            require(parts.stats[0][0] == parts.sorries[0][1], f"Stats must follow Sorries: {path}")
            pages += 1
    if (site / "data/site.json").is_file():
        shell = (site / "index.html").read_text()
        require(shell.count('data-lml-stats-navigation="true"') == 1,
                "Missing or duplicated Stats navigation integration")
        require((site / "stats/navigation.js").is_file(), "Missing Stats navigation script")
        pages += 2
    require(pages > 0, "No exposition navigation found")
    print(f"Validated {len(names)} declarations, links and navigation on {pages} pages", flush=True)
    return bundle


def wait(page, expression):
    deadline = time.monotonic() + 15
    while time.monotonic() < deadline:
        if page.value(expression):
            return
        time.sleep(.1)
    raise AssertionError(f"Browser check did not finish: {expression}")


def browser_checks(base, bundle, fixture, screenshots):
    for width in (1280, 390):
        page = Page(width=width, height=1000)
        try:
            page.ws.send("Emulation.setDeviceMetricsOverride", {
                "width": width, "height": 1000, "deviceScaleFactor": 1, "mobile": False})
            page.visit(base + "/stats/", "document.documentElement.dataset.statsReady === 'true'")
            require(page.value("innerWidth") == width, "Incorrect browser width")
            require(page.value("document.querySelector('#stats-bins').value") == "20", "Wrong default")
            for choice in ("10", "50", "exact", "20"):
                page.value(f"""(() => {{ const select = document.querySelector('#stats-bins');
                    select.value = {json.dumps(choice)}; select.dispatchEvent(new Event('change'));
                }})()""")
                require(page.value("[...document.querySelectorAll('.stats-bar')].reduce((s,b) => s + Number(b.dataset.count), 0)") ==
                        len(bundle["declarations"]), "Histogram does not cover every declaration")
                require(page.value("document.querySelector('.stats-bar').dataset.max") == "0",
                        "Zero uses lost their own bar")
            # Native buttons must support Enter and have a usable click target, including rare tail bars.
            targets = page.value("""[...document.querySelectorAll('.stats-bar:not(:disabled)')].map(b => {
                const r = b.getBoundingClientRect(); return {w:r.width,h:r.height}; })""")
            require(all(t["w"] >= 44 and t["h"] >= 44 for t in targets), "Chart targets are too small")
            page.value("document.querySelector('.stats-bar:not(:disabled)').focus()")
            page.ws.send("Input.dispatchKeyEvent", {"type": "keyDown", "key": "Enter", "code": "Enter",
                                                   "windowsVirtualKeyCode": 13, "text": "\r",
                                                   "unmodifiedText": "\r"})
            page.ws.send("Input.dispatchKeyEvent", {"type": "keyUp", "key": "Enter", "code": "Enter"})
            wait(page, "new URLSearchParams(location.search).has('min')")
            selected = page.value("location.href")
            expected = page.value("Number(document.querySelector('.stats-bar[aria-pressed=true]').dataset.count)")
            require(page.value("document.querySelectorAll('#stats-declarations tbody tr').length") ==
                    min(50, expected), "Bar selected the wrong number of declarations")
            if fixture:
                require(expected > 50, "Fixture did not exercise pagination")
                page.value("document.querySelector('#stats-next').click()")
                require(page.value("document.querySelector('#stats-page').textContent") == "Page 2 of 2",
                        "Pagination failed")
                page.value("history.back()")
                wait(page, "document.querySelector('#stats-page').textContent === 'Page 1 of 2'")
            page.visit(selected, "document.documentElement.dataset.statsReady === 'true'")
            require(page.value("!!document.querySelector('.stats-bar[aria-pressed=true]')"), "Shared range lost")
            page.value("document.querySelector('#stats-clear').click()")
            sample = next(d for d in bundle["declarations"] if d["name"] == "A") if fixture else bundle["declarations"][0]
            page.value(f"""(() => {{const input = document.querySelector('#stats-search');
                input.value = {json.dumps(sample['name'])}; input.dispatchEvent(new Event('input')); }})()""")
            row = page.value(f"""(() => {{const tr = [...document.querySelectorAll('#stats-declarations tbody tr')]
                .find(tr => tr.dataset.name === {json.dumps(sample['name'])});
                return tr ? [...tr.querySelectorAll('a')].map(a => a.href) : null; }})()""")
            require(row is not None and row[0] == base + "/" + sample["documentation"] and row[1] == sample["source"],
                    "Declaration links are incorrect")
            search_url = page.value("location.href")
            page.visit(search_url, "document.documentElement.dataset.statsReady === 'true'")
            require(page.value("document.querySelector('#stats-search').value") == sample["name"], "Shared search lost")
            # Horizontal scrolling is confined to the chart and declaration table.
            require(page.value("document.documentElement.scrollWidth <= innerWidth + 1"), "Page overflows on phone")
            require(not page.problems(), "Browser errors occurred")
            if screenshots:
                screenshots.mkdir(parents=True, exist_ok=True)
                page.value("document.querySelector('#stats-clear').click()")
                page.screenshot(screenshots / f"stats-{width}.png")
            # Open the actual documentation destination in the served exposition.
            selector = ('#nav-links a[data-lml-stats]' if bundle["build"].get("format") ==
                        "ltb-dataset/2" else '#toc a[href="stats/#stats"]')
            page.visit(row[0], f"!!document.querySelector({json.dumps(selector)})")
            require(page.value(f"document.querySelector({json.dumps(selector)}).textContent") == "Stats",
                    "Documentation page has no Stats navigation")
            print(f"Stats at {width}px: bar choices, keyboard, lists, links and shared URLs passed", flush=True)
        finally:
            page.close()


def check(site, fixture=False, screenshots=None):
    bundle = validate(site)

    class QuietHandler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *args):
            pass

    # Exercise the real Pages prefix and relative links, not just a server rooted at /stats/.
    with tempfile.TemporaryDirectory(prefix="lml-stats-web-") as temp:
        web = pathlib.Path(temp)
        (web / "LML").mkdir()
        (web / "LML/exposition").symlink_to(site.resolve(), target_is_directory=True)
        handler = functools.partial(QuietHandler, directory=str(web))
        with http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler) as server:
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            try:
                browser_checks(f"http://127.0.0.1:{server.server_port}/LML/exposition", bundle, fixture, screenshots)
            finally:
                server.shutdown()
                thread.join()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--site", type=pathlib.Path)
    parser.add_argument("--screenshots", type=pathlib.Path)
    args = parser.parse_args()
    subprocess.run([sys.executable, "-m", "unittest", "website_stats.checks"],
                   cwd=pathlib.Path(__file__).parent, check=True)
    subprocess.run(["node", str(pathlib.Path(__file__).parent / "website_stats/checks.js")], check=True)
    with tempfile.TemporaryDirectory(prefix="lml-stats-example-") as temp:
        project, site, data, _ = make_fixture(pathlib.Path(temp))
        build(data, site, project, REPOSITORY, REVISION)
        check(site, fixture=True, screenshots=args.screenshots)
    if args.site:
        check(args.site)


if __name__ == "__main__":
    main()
