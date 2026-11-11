#!/usr/bin/env python3
"""Check the links of the built HTML book: every cross-reference must reach an existing anchor.

Each section page embeds its pages as JSON (``<script id="document-data">``) with ``links``
(clickable regions) and ``anchors``/``headings`` (targets). A link ``#x`` must hit an id on its
own page; ``s05.html#x`` an id in that other page. Usage: verify_links.py BUILD_DIR
"""
from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from urllib.parse import unquote

DATA = re.compile(r'<script type="application/json" id="document-data">(.*?)</script>', re.S)


def load_pages(html_text: str) -> list[dict]:
    match = DATA.search(html_text)
    if not match:
        raise ValueError("no embedded document data")
    return json.loads(match.group(1))


def ids_and_links(pages: list[dict]) -> tuple[set[str], list[str]]:
    ids: set[str] = set()
    links: list[str] = []
    for page in pages:
        ids.update(a["id"] for a in page.get("anchors", []))
        ids.update(h["id"] for h in page.get("headings", []))
        links.extend(link["href"] for link in page.get("links", []))
    return ids, links


def broken_links(documents: dict[str, str]) -> list[str]:
    """``documents`` maps a file name to its HTML; returns one message per broken link."""
    targets: dict[str, set[str]] = {}
    links: dict[str, list[str]] = {}
    for name, text in documents.items():
        targets[name], links[name] = ids_and_links(load_pages(text))
    problems = []
    for name, hrefs in links.items():
        for href in hrefs:
            if href.startswith(("http://", "https://")):
                continue  # external (the blueprint website)
            page, _, fragment = href.partition("#")
            page = page or name
            if page not in targets:
                problems.append(f"{name}: link to missing page {page!r}")
            elif unquote(fragment) not in targets[page]:
                problems.append(f"{name}: no anchor {fragment!r} in {page}")
    return problems


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    files = sorted(Path(argv[1]).glob("s??.html"))
    if not files:
        print(f"no section pages in {argv[1]}", file=sys.stderr)
        return 2
    documents = {f.name: f.read_text(encoding="utf-8") for f in files}
    problems = broken_links(documents)
    total = sum(len(ids_and_links(load_pages(t))[1]) for t in documents.values())
    for message in problems:
        print(message)
    print(f"{total} links in {len(files)} pages, {len(problems)} broken.")
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
