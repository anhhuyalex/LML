#!/usr/bin/env python3
"""Write ``toc.json``: the contents of the whole book, read by the pane of every section page.

Each section page is typeset on its own and only knows its own headings, so the whole-book list is
assembled here from the finished pages. ``book-nav.js`` (next to the pages) fetches this file.

Usage: make_toc.py generated/sections.json OUTPUT_DIR [--pdf NAME.pdf]

OUTPUT_DIR must already hold ``s00.html`` ... (see ``build_talagrand_book.sh``).
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from verify_links import load_pages

# Links shown below the contents and at the foot of the landing page (relative to the book).
SITE_LINKS = (("Blueprint", "../blueprint/"), ("API documentation", "../docs/"), ("Home", "../"))


def section_entry(section: dict, page_file: Path) -> dict:
    """The entry of one section: its titles, size and headings below the section heading itself.

    The level-1 heading *is* the section, so the entry lists only the deeper headings.
    """
    if not page_file.is_file():
        raise FileNotFoundError(f"section page {page_file} is missing; build the HTML first")
    pages = load_pages(page_file.read_text(encoding="utf-8"))
    headings = [{"level": h["level"], "title": h["title"], "id": h["id"]}
                for page in pages for h in page.get("headings", []) if h["level"] > 1]
    return {"id": section["id"], "part": section["part"], "title": section["title"],
            "href": page_file.name, "pages": len(pages), "bytes": page_file.stat().st_size,
            "headings": headings}


def build_toc(sections_json: dict, output_dir: Path, pdf: str | None) -> dict:
    sections = [section_entry(s, output_dir / f"{s['id']}.html") for s in sections_json["sections"]]
    return {"title": sections_json["title"], "home": "./", "pdf": pdf,
            "links": [{"title": title, "href": href} for title, href in SITE_LINKS],
            "sections": sections}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    parser.add_argument("sections_json", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--pdf", help="file name of the whole-book PDF")
    args = parser.parse_args(argv)
    sections = json.loads(args.sections_json.read_text(encoding="utf-8"))
    toc = build_toc(sections, args.output_dir, args.pdf)
    (args.output_dir / "toc.json").write_text(
        json.dumps(toc, ensure_ascii=False, indent=1) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
