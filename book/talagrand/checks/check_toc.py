"""Checks for ``make_toc`` and the landing page's shared footer links."""
import json
import tempfile
import unittest
from pathlib import Path

import make_index
import make_toc

SECTIONS = {"title": "Book", "sections": [
    {"id": "s00", "part": 0, "title": "Intro"}, {"id": "s01", "part": 1, "title": "A & B"}]}


def page_with(*headings):
    return {"headings": [{"level": lv, "title": t, "id": i} for lv, t, i in headings]}


def write_page(directory: Path, name: str, *pages):
    text = '<script type="application/json" id="document-data">' + json.dumps(list(pages)) + "</script>"
    (directory / name).write_text(text, encoding="utf-8")


class TocChecks(unittest.TestCase):
    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)
        write_page(self.dir, "s00.html", page_with((1, "Intro", "heading-1")))
        write_page(self.dir, "s01.html", page_with((1, "1 A & B", "heading-1"), (2, "1.1 First", "heading-2")),
                   page_with((3, "1.1.1 Deep", "heading-3")), {"headings": []})

    def test_sections_keep_order_and_deeper_headings_only(self):
        toc = make_toc.build_toc(SECTIONS, self.dir, "book.pdf")
        self.assertEqual([s["id"] for s in toc["sections"]], ["s00", "s01"])
        self.assertEqual(toc["sections"][0]["headings"], [])        # the level-1 heading is the section
        self.assertEqual(toc["sections"][1]["headings"], [
            {"level": 2, "title": "1.1 First", "id": "heading-2"},
            {"level": 3, "title": "1.1.1 Deep", "id": "heading-3"}])

    def test_pages_size_and_links(self):
        toc = make_toc.build_toc(SECTIONS, self.dir, "book.pdf")
        section = toc["sections"][1]
        self.assertEqual((section["pages"], section["href"]), (3, "s01.html"))
        self.assertEqual(section["bytes"], (self.dir / "s01.html").stat().st_size)
        self.assertEqual((toc["home"], toc["pdf"]), ("./", "book.pdf"))
        self.assertEqual([l["href"] for l in toc["links"]], ["../blueprint/", "../docs/", "../"])

    def test_missing_section_page_is_an_error(self):
        (self.dir / "s01.html").unlink()
        with self.assertRaises(FileNotFoundError):
            make_toc.build_toc(SECTIONS, self.dir, None)

    def test_command_line_writes_toc_json(self):
        sections = self.dir / "sections.json"
        sections.write_text(json.dumps(SECTIONS), encoding="utf-8")
        self.assertEqual(make_toc.main([str(sections), str(self.dir), "--pdf", "book.pdf"]), 0)
        written = json.loads((self.dir / "toc.json").read_text(encoding="utf-8"))
        self.assertEqual(written["sections"][1]["title"], "A & B")

    def test_landing_page_footer_uses_the_same_links(self):
        page = make_index.render(SECTIONS, None)
        for title, href in make_toc.SITE_LINKS:
            self.assertIn(f'<a href="{href}">{title}</a>', page)


if __name__ == "__main__":
    unittest.main()
