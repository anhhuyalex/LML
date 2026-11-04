"""Meaningful small examples for counting, Referee compatibility, links and HTML edits."""
from __future__ import annotations

import copy
import json
import os
import pathlib
import subprocess
import sys
import tempfile
import unittest

from build_stats import build
from .example import REPOSITORY, REVISION, make_fixture
from .metrics import reuse
from .reader import authored, catalog, decode
from .render import PageParts, add_navigation


class StatsChecks(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.project, self.site, self.path, self.data = make_fixture(pathlib.Path(self.temp.name))

    def catalog(self):
        return catalog(self.data, self.site, self.project, REPOSITORY, REVISION)

    def test_distinct_users_and_public_population(self):
        declarations, excluded = self.catalog()
        counts = reuse(declarations, self.data)
        self.assertEqual(counts["A"], 4)  # B, D's statement, E's proof, explicitly named instance
        self.assertEqual(counts["B"], 1)  # C; B's self-reference is ignored
        self.assertEqual(counts["C"], 0)
        self.assertEqual(counts["Z000"], 0)
        self.assertNotIn("instFact", counts)
        self.assertNotIn("A.match_1", counts)
        self.assertNotIn("_private.Example.0.hidden", counts)
        self.assertEqual(sum(excluded.values()), 3)
        self.assertTrue(all(f"/blob/{REVISION}/" in d["source"] for d in declarations))

    def test_real_json_envelope_and_nested_sharing(self):
        self.assertEqual(decode(json.loads(self.path.read_text())), self.data)
        self.assertEqual(decode({"version": 16, "interned": [], "data": self.data}), self.data)
        for bad in [-1, 0, "0", True]:
            with self.assertRaisesRegex(ValueError, "reference"):
                decode({"version": 16, "interned": [], "data": {"$i": bad}})

    def test_refuse_unknown_format_and_partial_library(self):
        for mutation in [{"version": 17}, {"scope": {"mode": "claims"}},
                         {"scope": {"mode": "single"}}, {"thinDecls": [{}]}]:
            data = {**self.data, **mutation}
            with self.assertRaises(ValueError):
                decode({"version": 16, "interned": [], "data": data})

    def test_missing_docs_or_source_lines_fail(self):
        (self.site / "example/decl-A/index.html").unlink()
        with self.assertRaisesRegex(ValueError, "documentation"):
            self.catalog()
        self.data["decls"][0]["source"]["endLine"] = 10000
        with self.assertRaisesRegex(ValueError, "source lines"):
            self.catalog()

    def test_mismatched_site_and_unsafe_paths_fail(self):
        extra = copy.deepcopy(self.data["decls"][0])
        extra["name"] = "Missing"
        self.data["decls"].append(extra)
        with self.assertRaisesRegex(ValueError, "different declarations"):
            self.catalog()
        self.data["decls"].pop()
        self.data["decls"][0]["source"]["relPath"] = "../secret.lean"
        with self.assertRaisesRegex(ValueError, "source path"):
            self.catalog()

    def test_written_name_not_comments_or_generated_companion(self):
        self.assertTrue(authored("Ns.good", '/- theorem fake /- nested -/ -/\n theorem good : True := by trivial'))
        self.assertTrue(authored("Ns.quoted name", 'theorem «quoted name» : True := by trivial'))
        self.assertFalse(authored("Ns.good.match_1", 'theorem good : True := by trivial'))
        self.assertFalse(authored("Ns.hidden", 'private theorem hidden : True := by trivial'))
        self.assertFalse(authored("instFact", 'instance : Fact True := ⟨by trivial⟩'))
        self.assertTrue(authored("Ns.named", 'instance (priority := 100) named : Fact True := ⟨by trivial⟩'))
        self.assertFalse(authored("instFact", 'instance (priority := 100) : Fact True := ⟨by trivial⟩'))
        self.assertTrue(authored("Ns.left", 'alias ⟨Ns.left, Ns.right⟩ := pair_iff'))
        self.assertTrue(authored("Ns.right", 'alias ⟨Ns.left, Ns.right⟩ := pair_iff'))
        self.assertTrue(authored("Ns.Object", 'class inductive Object : Type | unit'))

    def test_navigation_after_sorries_and_repeatable_build(self):
        original = (self.site / "index.html").read_text()
        updated = add_navigation(original)
        parts = PageParts(updated)
        self.assertEqual(len(parts.stats), 1)
        self.assertEqual(parts.sorries[0][1], parts.stats[0][0])
        self.assertEqual(add_navigation(updated), updated)
        self.assertIn('<h1>Example</h1>', updated)
        with self.assertRaisesRegex(ValueError, "Sorries"):
            add_navigation(original.replace('href="sorries/#sorries"', 'href="gone/"'))
        for _ in range(2):
            bundle = build(self.path, self.site, self.project, REPOSITORY, REVISION)
            self.assertEqual(bundle["metrics"][0]["values"]["A"], 4)
            for path in self.site.rglob("*.html"):
                self.assertEqual(len(PageParts(path.read_text()).stats), 1)

    def test_command_entrypoints_outside_repository(self):
        # CI invokes the scripts directly. Package imports must work without a caller's
        # PYTHONPATH, current directory, or cached modules accidentally supplying files.
        scripts = pathlib.Path(__file__).resolve().parent.parent
        environment = {key: value for key, value in os.environ.items()
                       if key not in ("PYTHONPATH", "PYTHONHOME")}
        for command in ("build_stats.py", "check_stats.py"):
            with self.subTest(command=command):
                completed = subprocess.run(
                    [sys.executable, "-B", "-E", "-s", str(scripts / command), "--help"],
                    cwd=self.temp.name, env=environment, capture_output=True, text=True,
                )
                self.assertEqual(completed.returncode, 0, completed.stderr)
                self.assertIn("usage:", completed.stdout)


if __name__ == "__main__":
    unittest.main()
