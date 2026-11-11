"""Checks for label numbering (``tex2typ.index``) and text/math helpers (``tex2typ.text``)."""
import unittest
from pathlib import Path

from tex2typ.index import Index, talagrand_statement
from tex2typ.parser import Parser
from tex2typ.text import escape_line_start, escape_markup, normalize_math, typst_string
from tex2typ.errors import ConversionError

FIXTURE = Path(__file__).parent / "fixtures" / "mini.tex"
NBSP = "\u00a0"


def mini_index(overrides=None) -> Index:
    return Index(Parser(FIXTURE.read_text(), "mini.tex").parse_document(), overrides)


class NumberingChecks(unittest.TestCase):
    def test_section_numbers_follow_typst_headings(self):
        index = mini_index()
        self.assertEqual(index.labels["sec:mini:first"].number, "1")
        self.assertEqual(index.labels["sec:mini:second"].number, "1.1")

    def test_boxes_are_numbered_in_document_order(self):
        index = mini_index()
        self.assertEqual(index.labels["thm:mini:a"].number, "1")
        self.assertEqual(index.labels["lem:mini:b"].number, "2")
        self.assertEqual(index.labels["lem:mini:b"].part, 1)

    def test_talagrand_number_is_the_first_numbered_statement(self):
        index = mini_index()
        self.assertEqual(index.labels["thm:mini:a"].tal_number, "1.2.3")
        self.assertEqual(index.labels["thm:mini:a"].tal_kind, "Theorem")

    def test_equation_only_tags_have_no_number(self):
        document = Parser("\\chapter{x}\n\\section{s}\n\\begin{lemma}\\label{l}\\talsource{Eq.~(1.12)}\nA.\\end{lemma}").parse_document()
        self.assertIsNone(Index(document).labels["l"].tal_number)

    def test_statements_sharing_a_number_are_marked(self):
        index = mini_index()
        self.assertTrue(index.labels["thm:mini:a"].shared)  # lemma b cites 1.2.3 too

    def test_override_can_replace_or_remove_a_number(self):
        index = mini_index({"thm:mini:a": "Proposition 9.9.9", "lem:mini:b": ""})
        self.assertEqual(index.labels["thm:mini:a"].tal_number, "9.9.9")
        self.assertIsNone(index.labels["lem:mini:b"].tal_number)
        self.assertFalse(index.labels["thm:mini:a"].shared)

    def test_duplicate_labels_are_an_error(self):
        document = Parser("\\chapter{x}\n\\section{s}\\label{a}\n\\subsection{t}\\label{a}").parse_document()
        with self.assertRaisesRegex(ConversionError, "duplicate label a"):
            Index(document)


class ReferenceTextChecks(unittest.TestCase):
    def test_shared_numbers_show_the_serial_too(self):
        index = mini_index()
        self.assertEqual(index.ref_text("thm:mini:a", "Theorem"), f"Theorem{NBSP}1.2.3 [#1]")
        self.assertEqual(index.ref_text("thm:mini:a"), "1.2.3 [#1]")

    def test_unique_numbers_show_only_the_talagrand_number(self):
        index = mini_index({"lem:mini:b": ""})
        self.assertEqual(index.ref_text("thm:mini:a", "Lemma"), f"Theorem{NBSP}1.2.3")

    def test_box_without_talagrand_number_uses_its_own_kind_and_serial(self):
        index = mini_index({"lem:mini:b": ""})
        self.assertEqual(index.ref_text("lem:mini:b", "Theorem"), f"Lemma{NBSP}2")
        self.assertEqual(index.ref_text("lem:mini:b"), "2")

    def test_sections_and_external_labels(self):
        index = mini_index()
        self.assertEqual(index.ref_text("sec:mini:second", "Section"), f"Section{NBSP}1.1")
        self.assertEqual(index.ref_text("thm:other:x", "Theorem"), f"Theorem{NBSP}[thm:other:x]")
        self.assertTrue(index.is_external("thm:other:x"))

    def test_talagrand_statement_parser(self):
        from tex2typ.model import Text
        found = talagrand_statement([Text(f"Lemmas{NBSP}1.6.2--1.6.4, Eq.{NBSP}(1.1)")])
        self.assertEqual(found, ("Lemma", "1.6.2"))
        self.assertIsNone(talagrand_statement([Text(f"Eq.{NBSP}(1.12)")]))


class TextChecks(unittest.TestCase):
    def test_markup_characters_are_escaped(self):
        self.assertEqual(escape_markup("a_b #c $d [e] <f> @g //h"),
                         "a\\_b \\#c \\$d \\[e\\] \\<f\\> \\@g \\/\\/h")

    def test_whitespace_is_collapsed(self):
        self.assertEqual(escape_markup("a \n  b\t c"), "a b c")

    def test_list_and_heading_markers_at_paragraph_start(self):
        self.assertEqual(escape_line_start("- item"), "\\- item")
        self.assertEqual(escape_line_start("= x"), "\\= x")
        self.assertEqual(escape_line_start("12. x"), "12\\. x")
        self.assertEqual(escape_line_start("plain - text"), "plain - text")

    def test_string_literals(self):
        self.assertEqual(typst_string('a"b\\c'), '"a\\"b\\\\c"')

    def test_math_normalisation(self):
        resolved = lambda label, prefix: f"<{prefix}:{label}#1>"
        result = normalize_math(r"\text{Lemma~\ref{l}, \ref{m}} B=\begin{psmallmatrix}1&1\end{psmallmatrix}", resolved)
        self.assertIn(r"\text{<Lemma:l\#1>, <None:m\#1>}", result)
        self.assertIn(r"\left(\begin{smallmatrix}1&1\end{smallmatrix}\right)", result)

    def test_backticks_in_math_are_rejected(self):
        with self.assertRaises(ConversionError):
            normalize_math("a`b", lambda *_: "")


if __name__ == "__main__":
    unittest.main()
