"""Checks for books made of several chapter files (``chapters.merge_chapters`` and ``convert``)."""
import json
import tempfile
import unittest
from pathlib import Path

from sample_files import MINI_SECOND_TEX, MINI_TEX
from tex2typ.chapters import merge_chapters
from tex2typ.cli import convert
from tex2typ.errors import ConversionError
from tex2typ.index import Index
from tex2typ.model import Document, Heading, Text
from tex2typ.parser import parse_file


def merged() -> Document:
    return merge_chapters([parse_file(MINI_TEX), parse_file(MINI_SECOND_TEX)])


class MergeChecks(unittest.TestCase):
    def test_sections_continue_and_later_chapter_opens_its_first_section(self):
        first, second = parse_file(MINI_TEX), parse_file(MINI_SECOND_TEX)
        book = merge_chapters([first, second])
        self.assertEqual(len(book.sections), len(first.sections) + len(second.sections))
        opening = book.sections[len(first.sections)]
        self.assertEqual((opening[0].level, opening[0].label), (0, "chap:mini2"))
        self.assertIn(second.sections[0][0], opening)       # its own section heading follows
        self.assertEqual([b for b in book.front if isinstance(b, Heading)][0].label, "chap:mini")

    def test_inputs_are_not_modified(self):
        first, second = parse_file(MINI_TEX), parse_file(MINI_SECOND_TEX)
        before = (len(first.front), len(second.sections[0]))
        merge_chapters([first, second])
        self.assertEqual((len(first.front), len(second.sections[0])), before)

    def test_chapter_without_a_section_is_an_error(self):
        empty = Document([Text("Empty")], "chap:empty")
        with self.assertRaises(ConversionError):
            merge_chapters([parse_file(MINI_TEX), empty])

    def test_no_chapter_is_an_error(self):
        with self.assertRaises(ConversionError):
            merge_chapters([])


class NumberingChecks(unittest.TestCase):
    def setUp(self):
        self.labels = Index(merged()).labels

    def test_chapters_are_numbered_and_resolve_as_references(self):
        self.assertEqual((self.labels["chap:mini"].kind, self.labels["chap:mini"].number), ("chapter", "1"))
        self.assertEqual(self.labels["chap:mini2"].number, "2")
        index = Index(merged())
        self.assertEqual(index.ref_text("chap:mini", "Chapter"), "Chapter\u00a01")
        self.assertFalse(index.is_external("chap:mini"))

    def test_sections_continue_across_chapters(self):
        first_sections = len(parse_file(MINI_TEX).sections)
        self.assertEqual(self.labels["sec:mini2:only"].part, first_sections + 1)
        self.assertEqual(self.labels["sec:mini2:only"].number, str(first_sections + 1))

    def test_statement_numbers_restart_per_chapter_and_carry_the_chapter_after_the_first(self):
        self.assertEqual(self.labels["thm:mini:a"].number, "1")          # unchanged for chapter 1
        self.assertEqual(self.labels["lem:mini2:c"].number, "2.1")
        self.assertEqual(self.labels["rem:mini2:d"].number, "2.2")
        self.assertEqual(self.labels["lem:mini2:c"].tal_number, "2.1.1")


class ConvertChecks(unittest.TestCase):
    def convert_both(self):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        out = Path(directory.name)
        return out, convert([MINI_TEX, MINI_SECOND_TEX], out)

    def test_section_table_and_titles(self):
        _, summary = self.convert_both()
        titles = [s["title"] for s in summary["sections"]]
        self.assertEqual(titles, ["Introduction and conventions", "First section", "Only section"])
        self.assertEqual([s["id"] for s in summary["sections"]], ["s00", "s01", "s02"])

    def test_generated_files(self):
        out, _ = self.convert_both()
        second = (out / "body" / "s02.typ").read_text(encoding="utf-8")
        self.assertTrue(second.index("#heading(numbering: none)[Second mini chapter] <chap:mini2>")
                        < second.index("= Only section"))
        self.assertIn('#thm("lemma", "2.1", tal: ("Lemma", "2.1.1")', second)
        self.assertIn('Chapter\u00a0#rf("chap:mini", "1", section: "s00");', second)
        first = (out / "body" / "s01.typ").read_text(encoding="utf-8")
        self.assertIn('#thm("theorem", 1,', first)                       # a plain number stays a number
        self.assertIn("<chap:mini>", (out / "body" / "s00.typ").read_text(encoding="utf-8"))
        names = json.loads((out / "lean-names.json").read_text(encoding="utf-8"))
        self.assertIn("Nat.add_zero", names)

    def test_a_single_path_still_works(self):
        with tempfile.TemporaryDirectory() as directory:
            summary = convert(MINI_TEX, Path(directory))
            self.assertEqual(len(summary["sections"]), 2)


if __name__ == "__main__":
    unittest.main()
