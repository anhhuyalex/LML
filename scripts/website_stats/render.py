"""Preserve Referee's shell and add navigation by parsing HTML, not replacing arbitrary text."""
from __future__ import annotations

import json
import pathlib
import shutil
from html.parser import HTMLParser

from .reader import require


class PageParts(HTMLParser):
    def __init__(self, text):
        super().__init__(convert_charrefs=False)
        self.text = text
        self.lines = [0]
        for line in text.splitlines(keepends=True):
            self.lines.append(self.lines[-1] + len(line))
        self.spans = {}
        self.starts = {}
        self.nav = []
        self.has_toc = False
        self.row = None
        self.sorries = []
        self.stats = []
        self.feed(text)

    def position(self):
        line, column = self.getpos()
        return self.lines[line - 1] + column

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        start = self.position()
        if tag in ("main", "title"):
            require(tag not in self.starts and tag not in self.spans, f"Duplicate <{tag}>")
            self.starts[tag] = start
        if tag == "base":
            self.spans["base"] = (start, start + len(self.get_starttag_text()))
        if tag == "head":
            self.spans["head_open"] = (start, start + len(self.get_starttag_text()))
        if tag == "nav":
            self.nav.append(attrs.get("id") == "toc")
            self.has_toc |= self.nav[-1]
        if tag == "tr" and any(self.nav):
            self.row = {"start": start, "sorries": False, "stats": False}
        if tag == "a" and self.row is not None:
            href = attrs.get("href", "").split("#")[0]
            self.row["sorries"] |= href == "sorries/"
            self.row["stats"] |= href == "stats/"

    def handle_endtag(self, tag):
        end = self.position() + len(tag) + 3
        if tag in self.starts:
            self.spans[tag] = (self.starts.pop(tag), end)
        if tag == "head":
            self.spans["head_end"] = (self.position(), self.position())
        if tag == "tr" and self.row is not None:
            for key in ("sorries", "stats"):
                if self.row[key]:
                    getattr(self, key).append((self.row["start"], end))
            self.row = None
        if tag == "nav" and self.nav:
            self.nav.pop()


def edited(text, edits):
    for start, end, replacement in sorted(edits, reverse=True):
        text = text[:start] + replacement + text[end:]
    return text


NAV_ROW = ('<tr class="unnumbered" data-lml-stats="true"><td class="num"></td>'
           '<td><a href="stats/#stats">Stats</a></td></tr>')


def add_navigation(text):
    parts = PageParts(text)
    if not parts.has_toc:
        return text
    require(len(parts.sorries) == 1, "Expected one Sorries navigation row; check the Referee pin")
    require(len(parts.stats) <= 1, "Duplicate Stats navigation entries")
    edits = [(start, end, "") for start, end in parts.stats]
    end = parts.sorries[0][1]
    edits.append((end, end, NAV_ROW))
    return edited(text, edits)


CONTENT = """<main><div class="content-wrapper lml-stats">
<section aria-labelledby="stats"><h1 id="stats">Stats</h1>
<p id="stats-version"></p><p id="stats-population"></p>
<p>These counts describe the library's shape. They are not a quality score.</p>
<div id="stats-controls"><label>Statistic <select id="stats-metric"></select></label>
<label>Number of bars <select id="stats-bins"><option>10</option>
<option selected>20</option><option>50</option><option value="exact">One per exact count</option>
</select></label></div>
<h2 id="stats-chart-title"></h2><p id="stats-explanation"></p>
<details><summary>How the counts work</summary><p id="stats-notes"></p></details>
<p id="stats-y-label"></p><div id="stats-chart" aria-labelledby="stats-chart-title"></div>
<p id="stats-x-label"></p>
<details><summary>Show the chart as a table</summary>
<table id="stats-counts"><caption>Histogram counts</caption><thead><tr>
<th scope="col">Uses</th><th scope="col">Number of declarations</th></tr></thead><tbody></tbody></table>
</details>
<p><a href="stats/data.json" download="lml-statistics.json">Download statistics as JSON</a></p>
<h2 id="stats-selection" tabindex="-1">Declarations</h2>
<div id="stats-list-controls"><label>Search declarations
<input type="search" id="stats-search" placeholder="Name or module"></label>
<button id="stats-clear" type="button">Show all declarations</button></div>
<p id="stats-count" role="status" aria-live="polite"></p>
<div class="stats-table-scroll"><table id="stats-declarations"><thead><tr>
<th scope="col">Declaration</th><th scope="col">Kind</th><th scope="col">Module</th>
<th scope="col">Uses</th><th scope="col">Links</th></tr></thead><tbody></tbody></table></div>
<nav id="stats-pagination" aria-label="Declaration list pages"><button id="stats-prev">Previous</button>
<span id="stats-page"></span><button id="stats-next">Next</button></nav>
<noscript>Enable JavaScript to use the interactive chart. The JSON download contains every count.</noscript>
<p id="stats-error" role="alert" hidden></p>
</section></div></main>"""


def build_site(site: pathlib.Path, bundle):
    # The home page gives us the matching header, styles, theme and sidebar, without Browse's table.
    text = (site / "index.html").read_text()
    parts = PageParts(text)
    for name in ("main", "title", "base", "head_end"):
        require(name in parts.spans, f"Missing exposition shell element: {name}")
    require(parts.has_toc, "The exposition shell has no table of contents")
    edits = [(*parts.spans["main"], CONTENT),
             (*parts.spans["title"], "<title>Stats — Lean Machine Learning</title>"),
             (*parts.spans["base"], '<base href="../">'),
             (*parts.spans["head_end"],
              '<link rel="stylesheet" href="stats/stats.css">'
              '<script src="stats/stats.js" defer></script>')]
    out = site / "stats"
    out.mkdir(exist_ok=True)
    (out / "index.html").write_text(edited(text, edits))
    (out / "data.json").write_text(json.dumps(bundle, ensure_ascii=False, indent=2) + "\n")
    assets = pathlib.Path(__file__).parent / "assets"
    for name in ("stats.js", "stats.css"):
        shutil.copyfile(assets / name, out / name)
    pages = 0
    for path in sorted(site.rglob("*.html")):
        original = path.read_text()
        updated = add_navigation(original)
        if NAV_ROW in updated:
            pages += 1
        if updated != original:
            path.write_text(updated)
    require(pages, "No exposition navigation was updated")
    return pages
