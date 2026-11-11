"""Checks for ``verify_links`` and for the cache logic added to the vendored ``build.py``."""
import json
import sys
import tempfile
import unittest
from pathlib import Path

import verify_links

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "typstverso"))
import build  # noqa: E402  (vendored TypstVerso driver)


def page(anchors=(), links=(), headings=()):
    return {"anchors": [{"id": i} for i in anchors], "links": [{"href": h} for h in links],
            "headings": [{"id": i} for i in headings]}


def html(*pages):
    return ('<script type="application/json" id="document-data">'
            + json.dumps(list(pages)) + "</script>")


class LinkChecks(unittest.TestCase):
    def test_valid_links_in_page_and_across_pages(self):
        docs = {"s01.html": html(page(anchors=["thm:a"], links=["#thm:a", "s02.html#sec:b", "https://x.org/"])),
                "s02.html": html(page(headings=["heading-1"], anchors=["sec:b"]))}
        self.assertEqual(verify_links.broken_links(docs), [])

    def test_missing_anchor_and_page_are_reported(self):
        docs = {"s01.html": html(page(links=["#nope", "s09.html#x", "s02.html#nope"])),
                "s02.html": html(page())}
        problems = verify_links.broken_links(docs)
        self.assertEqual(len(problems), 3)
        self.assertTrue(any("missing page 's09.html'" in p for p in problems))

    def test_pages_without_embedded_data_are_an_error(self):
        with self.assertRaises(ValueError):
            verify_links.load_pages("<html></html>")


class CacheChecks(unittest.TestCase):
    def test_compaction_round_trip_shares_tooltips(self):
        token = lambda text, tip: {"kind": "const", "text": text, "tooltip": tip}
        data = {"schemaVersion": 1, "inlineCommands": [
            {"lines": [[token("a", "long tip"), token("b", "long tip"), token("c", "")]]}]}
        compact = build.compact_cache(data)
        self.assertEqual(compact["tooltips"], ["long tip", ""])
        self.assertNotIn("tooltip", json.dumps(compact["inlineCommands"]))
        self.assertEqual(build.expand_cache(compact), data)

    def test_expand_accepts_data_that_was_never_compacted(self):
        data = {"declarations": {}, "commands": []}
        self.assertEqual(build.expand_cache(data), data)

    def project(self, directory: Path) -> Path:
        project = directory / "lean"
        project.mkdir()
        (project / "lean-toolchain").write_text("leanprover/lean4:v4.36.0\n")
        (project / "lake-manifest.json").write_text("{}")
        (project / "Some.lean").write_text("def x := 1")
        return project

    def builder(self, project: Path, directory: Path) -> "build.Builder":
        return build.Builder(project, directory, None, ["Some"], False, "html", directory,
                             directory, "book", prebuilt=True, export_script=build.EXPORT_SCRIPT)

    def test_prebuilt_fingerprint_ignores_lean_sources_but_not_the_pins(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            project = self.project(directory)
            before = self.builder(project, directory).fingerprint
            (project / "Some.lean").write_text("def x := 2  -- edited")
            self.assertEqual(self.builder(project, directory).fingerprint, before)
            (project / "lake-manifest.json").write_text('{"changed": true}')
            self.assertNotEqual(self.builder(project, directory).fingerprint, before)

    def test_config_snapshot_depends_on_content_not_modification_time(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = self.project(Path(tmp))
            first = build.config_snapshot(project)
            (project / "lean-toolchain").write_text("leanprover/lean4:v4.36.0\n")  # same content, new mtime
            self.assertEqual(build.config_snapshot(project), first)


if __name__ == "__main__":
    unittest.main()
