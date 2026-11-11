"""Checks for ``make_index``."""
import json
import tempfile
import unittest
from pathlib import Path

import make_index

SECTIONS = {"title": "Chapter <One>", "sections": [
    {"id": "s00", "part": 0, "title": "Intro"}, {"id": "s01", "part": 1, "title": "A & B"}]}


class IndexPageChecks(unittest.TestCase):
    def test_links_titles_and_escaping(self):
        page = make_index.render(SECTIONS, "book.pdf")
        self.assertIn('<a href="s01.html"><span class="number">1</span>A &amp; B</a>', page)
        self.assertIn('<a href="s00.html"><span class="number"></span>Intro</a>', page)
        self.assertIn("Chapter &lt;One&gt;", page)
        self.assertIn('<a href="book.pdf">Whole book (PDF)</a>', page)

    def test_no_pdf_link_when_not_requested(self):
        self.assertNotIn("Whole book", make_index.render(SECTIONS, None))

    def test_command_line_writes_index_html(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "sections.json"
            source.write_text(json.dumps(SECTIONS))
            self.assertEqual(make_index.main([str(source), str(Path(directory) / "out")]), 0)
            self.assertTrue((Path(directory) / "out" / "index.html").is_file())


if __name__ == "__main__":
    unittest.main()
