#!/usr/bin/env python3
"""Write ``index.html``: the landing page of the per-section HTML book.

Usage: make_index.py generated/sections.json OUTPUT_DIR [--pdf NAME.pdf]
"""
from __future__ import annotations

import argparse
import html
import json
from pathlib import Path

PAGE = """<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>{title}</title>
<style>
  body {{ margin: 0; background: #eeeae3; color: #343b36; font: 16px/1.5 system-ui, sans-serif; }}
  main {{ max-width: 760px; margin: auto; padding: 32px 20px 64px; }}
  h1 {{ font: 600 28px/1.25 Georgia, serif; margin: 0 0 12px; }}
  p.lead {{ color: #4b524d; }}
  ol {{ padding: 0; list-style: none; display: grid; gap: 4px; margin: 24px 0; }}
  li a {{ display: block; padding: 8px 12px; border-radius: 6px; color: inherit; text-decoration: none; background: #fff; }}
  li a:hover {{ background: #dfe9f4; }}
  .number {{ display: inline-block; min-width: 2.2em; color: #626a64; }}
  footer {{ color: #626a64; font-size: 14px; }}
  footer a {{ color: #245b96; }}
</style>
</head>
<body>
<main>
<h1>{title}</h1>
<p class="lead">A book version of the Lean blueprint chapter. Every statement shows its Talagrand number
and the signature of the Lean declaration that proves it; hover over Lean code for types and documentation.</p>
<ol>
{items}
</ol>
<footer>{pdf} <a href="../blueprint/">Blueprint</a> · <a href="../docs/">API documentation</a> · <a href="../">Home</a></footer>
</main>
</body>
</html>
"""


def render(sections_json: dict, pdf: str | None) -> str:
    items = []
    for section in sections_json["sections"]:
        number = "" if section["part"] == 0 else str(section["part"])
        items.append(f'<li><a href="{section["id"]}.html"><span class="number">{number}</span>'
                     f'{html.escape(section["title"])}</a></li>')
    pdf_link = f'<a href="{html.escape(pdf)}">Whole book (PDF)</a> · ' if pdf else ""
    return PAGE.format(title=html.escape(sections_json["title"]), items="\n".join(items), pdf=pdf_link)


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("sections_json", type=Path)
    parser.add_argument("output_dir", type=Path)
    parser.add_argument("--pdf", help="file name of the whole-book PDF, linked from the page")
    args = parser.parse_args(argv)
    page = render(json.loads(args.sections_json.read_text(encoding="utf-8")), args.pdf)
    args.output_dir.mkdir(parents=True, exist_ok=True)
    (args.output_dir / "index.html").write_text(page, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
