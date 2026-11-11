"""Checks for the LaTeX parser (``tex2typ.parser``)."""
import unittest
from pathlib import Path

from tex2typ.errors import ConversionError
from tex2typ.model import (DisplayMath, Environment, Heading, ListBlock, Math, Meta, Paragraph,
                           Proof, Ref, RunInHead, Styled, Text)
from tex2typ.parser import Parser, strip_comments

FIXTURE = Path(__file__).parent / "fixtures" / "mini.tex"


def blocks(source: str):
    return Parser(source).parse_blocks(0, len(source))


def text_of(inlines) -> str:
    return "".join(n.value for n in inlines if isinstance(n, Text))


class InlineChecks(unittest.TestCase):
    def inline(self, source: str):
        (paragraph,) = blocks(source)
        return paragraph.inlines

    def test_accents_quotes_and_nonbreaking_space(self):
        text = text_of(self.inline(r"H\"older's ``quoted'' Lata\l{}a Gr\"{o}nwall a~b"))
        self.assertEqual(text, "Hölder's “quoted” Latała Grönwall a\u00a0b")

    def test_escaped_characters_and_spacing(self):
        self.assertEqual(text_of(self.inline(r"50\% of \_x\_ and a\ b")), "50% of _x_ and a b")

    def test_math_is_kept_verbatim(self):
        (node,) = [n for n in self.inline(r"see $a_{ij}\le \frac12$ here") if isinstance(n, Math)]
        self.assertEqual(node.src, r"a_{ij}\le \frac12")

    def test_ref_takes_the_word_before_it_as_prefix(self):
        refs = [n for n in self.inline(r"Theorem~\ref{a} and \ref{b}") if isinstance(n, Ref)]
        self.assertEqual([(r.label, r.prefix) for r in refs], [("a", "Theorem"), ("b", None)])

    def test_styled_text_nests_math(self):
        (styled,) = [n for n in self.inline(r"\texttt{Fin 2 $\to$ Nat}") if isinstance(n, Styled)]
        self.assertEqual(styled.style, "mono")
        self.assertTrue(any(isinstance(c, Math) for c in styled.children))

    def test_comments_are_blanked_without_moving_offsets(self):
        source = "a % hidden\nb \\% shown"
        self.assertEqual(len(strip_comments(source)), len(source))
        self.assertNotIn("hidden", strip_comments(source))
        self.assertIn("\\%", strip_comments(source))

    def test_unsupported_command_reports_its_line(self):
        with self.assertRaisesRegex(ConversionError, r"<tex>:3: unsupported command \\cite"):
            blocks("one\n\ntwo \\cite{x}")


class BlockChecks(unittest.TestCase):
    def test_math_environments_inside_inline_math_are_not_environments(self):
        (paragraph,) = blocks(r"so $B=\begin{pmatrix}1&2\\3&4\end{pmatrix}$ holds")
        self.assertIsInstance(paragraph, Paragraph)

    def test_display_math_forms(self):
        result = blocks("a\n\\[ x=1 \\]\n$$y=2,$$\n\\begin{align*}z&=3\\end{align*}\n")
        displays = [b.src for b in result if isinstance(b, DisplayMath)]
        self.assertEqual(displays[:2], ["x=1", "y=2,"])
        self.assertTrue(displays[2].startswith("\\begin{align*}"))

    def test_environment_metadata_is_harvested(self):
        (env,) = blocks(
            "\\begin{lemma}[Title]\\label{lem:x}\n\\lean{A.b,\n  C.d}\n\\leanok\n"
            "\\talsource{Lemma~1.2.3, $\\beta$}\nBody.\n\\end{lemma}")
        self.assertIsInstance(env, Environment)
        self.assertEqual((env.kind, env.label, env.lean), ("lemma", "lem:x", ["A.b", "C.d"]))
        self.assertEqual(text_of(env.title), "Title")
        self.assertIn("1.2.3", text_of(env.source))
        self.assertEqual(text_of(env.blocks[0].inlines).strip(), "Body.")

    def test_environment_holding_only_metadata_has_no_empty_paragraph(self):
        (env,) = blocks("\\begin{remark}\\label{r}\\leanok\n\\end{remark}")
        self.assertEqual(env.blocks, [])

    def test_proof_drops_blueprint_commands(self):
        (proof,) = blocks("\\begin{proof}\n\\leanok\n\\uses{a,b}\nText.\n\\end{proof}")
        self.assertIsInstance(proof, Proof)
        self.assertEqual(len(proof.blocks), 1)
        self.assertFalse(any(isinstance(n, Meta) for n in proof.blocks[0].inlines))

    def test_nested_lists_and_item_markers(self):
        (outer,) = blocks("\\begin{itemize}\n\\item a\n\\item b\n\\begin{enumerate}\n"
                          "\\item c\n\\item d\n\\end{enumerate}\n\\end{itemize}")
        self.assertIsInstance(outer, ListBlock)
        self.assertEqual(len(outer.items), 2)
        inner = [b for b in outer.items[1].blocks if isinstance(b, ListBlock)]
        self.assertTrue(inner[0].ordered)
        (labelled,) = blocks("\\begin{itemize}\\item[A.] x \\item[B.] y\\end{itemize}")
        self.assertEqual([text_of(i.marker) for i in labelled.items], ["A.", "B."])

    def test_run_in_head(self):
        result = blocks("\\paragraph{Head.} Then text.")
        self.assertIsInstance(result[0], RunInHead)
        self.assertIsInstance(result[1], Paragraph)

    def test_heading_label_may_follow_on_the_next_line(self):
        (heading,) = blocks("\\subsection{Title $x$}\n\\label{sec:x}")
        self.assertEqual((heading.level, heading.label), (2, "sec:x"))

    def test_unknown_environment_is_rejected(self):
        with self.assertRaisesRegex(ConversionError, "unsupported environment tikzpicture"):
            blocks("\\begin{tikzpicture}x\\end{tikzpicture}")


class DocumentChecks(unittest.TestCase):
    def test_fixture_structure(self):
        document = Parser(FIXTURE.read_text(), "mini.tex").parse_document()
        self.assertEqual(document.label, "chap:mini")
        self.assertEqual(len(document.front), 1)
        self.assertEqual(len(document.sections), 1)
        self.assertIsInstance(document.sections[0][0], Heading)

    def test_a_document_needs_exactly_one_chapter(self):
        with self.assertRaises(ConversionError):
            Parser("\\section{x}").parse_document()


if __name__ == "__main__":
    unittest.main()
