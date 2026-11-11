"""Checks for the Typst emitter and the generated files, including a Typst compile."""
import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from tex2typ.cli import convert
from tex2typ.emit import Emitter
from tex2typ.index import Index
from tex2typ.parser import Parser

HERE = Path(__file__).parent
BOOK = HERE.parent
FIXTURE = HERE / "fixtures" / "mini.tex"
CHAPTER = BOOK.parent.parent / "blueprint" / "src" / "chapters" / "spinglasses_talagrand.tex"
TYPST = shutil.which("typst")


def emit_fixture() -> str:
    document = Parser(FIXTURE.read_text(), "mini.tex").parse_document()
    index = Index(document)
    return Emitter(index, 1).blocks(document.sections[0])


class EmitChecks(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.output = emit_fixture()

    def test_theorem_box_arguments(self):
        self.assertIn('#thm("theorem", 1, tal: ("Theorem", "1.2.3"), title: [A title with #mi(`x^2`);]', self.output)
        self.assertIn('label: "thm:mini:a"', self.output)
        self.assertIn('names: ("Nat.add_comm", "Nat.mul_comm",)', self.output)

    def test_references_are_resolved_by_the_converter(self):
        self.assertIn('#rf("sec:mini:second", "Section\u00a01.1");', self.output)
        self.assertIn('external: true', self.output)

    def test_math_forms(self):
        self.assertIn("#mitex(`\\sum_{i<n} i", self.output)
        self.assertIn("Lemma\u00a01.2.3 [\\#2]", self.output)  # \ref inside \text{} in math; # escaped
        self.assertIn("\\left(\\begin{smallmatrix}", self.output)

    def test_run_in_head_joins_the_next_paragraph(self):
        self.assertIn("#run-in[Run-in.]; Text after a run-in head", self.output)

    def test_lists(self):
        self.assertIn("#list(tight: false,", self.output)
        self.assertIn("#enum(tight: false,", self.output)
        self.assertIn("#labeled-items(", self.output)

    def test_escaping_of_special_characters(self):
        self.assertIn("50% of", self.output)


@unittest.skipUnless(TYPST, "typst is not installed")
class TypstCompileChecks(unittest.TestCase):
    """The generated markup must be valid Typst. Lean results are not needed in discovery mode."""

    def compile(self, entry: Path) -> subprocess.CompletedProcess:
        return subprocess.run(
            [TYPST, "compile", "--root", str(BOOK.parent), "--input", "lean-discover=true",
             str(entry), str(entry.with_suffix(".pdf"))], capture_output=True, text=True)

    def generated_dir(self, name: str) -> Path:
        directory = Path(tempfile.mkdtemp(prefix=name + "-", dir=BOOK / ".check-build"))
        self.addCleanup(shutil.rmtree, directory, ignore_errors=True)
        return directory

    @classmethod
    def setUpClass(cls):
        (BOOK / ".check-build").mkdir(exist_ok=True)

    def test_fixture_compiles_as_book_and_as_section(self):
        out = self.generated_dir("mini")
        convert(FIXTURE, out)
        for entry in ("book.typ", "s00.typ", "s01.typ"):
            result = self.compile(out / entry)
            self.assertEqual(result.returncode, 0, entry + ": " + result.stderr)

    @unittest.skipUnless(CHAPTER.is_file(), "blueprint chapter not found")
    def test_real_chapter_compiles(self):
        out = self.generated_dir("chapter")
        summary = convert(CHAPTER, out)
        self.assertEqual(len(summary["sections"]), 15)
        result = self.compile(out / "book.typ")
        self.assertEqual(result.returncode, 0, result.stderr[-2000:])

    @unittest.skipUnless(CHAPTER.is_file(), "blueprint chapter not found")
    def test_heading_numbers_agree_with_the_converter(self):
        """Section references are computed by the converter; Typst must number headings alike."""
        out = self.generated_dir("numbers")
        convert(CHAPTER, out)
        expression = """query(heading).filter(h => h.has("label")).map(h =>
          (str(h.label), numbering(h.numbering, ..counter(heading).at(h.location()))))"""
        result = subprocess.run(
            [TYPST, "eval", "--root", str(BOOK.parent), "--input", "lean-discover=true",
             "--in", str(out / "book.typ"), expression], capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr[-2000:])
        typst_numbers = dict(json.loads(result.stdout))
        converter = {k: v["number"] for k, v in json.loads((out / "labels.json").read_text()).items()
                     if v["kind"] == "section"}
        self.assertGreater(len(converter), 20)
        self.assertEqual(typst_numbers, converter)


if __name__ == "__main__":
    unittest.main()
