"""Escaping of plain text and normalisation of math for Typst."""
from __future__ import annotations

import re
from typing import Callable

from .errors import ConversionError

MARKUP_SPECIAL = re.compile(r"[\\#$*_`@<>\[\]/~]")
LEADING_MARKER = re.compile(r"^(\s*)([-+=]|\d+\.)")


def escape_markup(text: str) -> str:
    """Escape characters that Typst markup would interpret, after collapsing whitespace."""
    text = re.sub(r"[ \t\n]+", " ", text)
    return MARKUP_SPECIAL.sub(lambda m: "\\" + m.group(), text)


def escape_line_start(line: str) -> str:
    """Stop ``- ``, ``+ ``, ``= `` and ``1.`` at the start of a paragraph becoming lists/headings."""
    m = LEADING_MARKER.match(line)
    if not m:
        return line
    marker = m.group(2)
    escaped = "\\" + marker if len(marker) == 1 else marker[:-1] + "\\."
    return m.group(1) + escaped + line[m.end():]


def typst_string(value: str) -> str:
    """A Typst string literal."""
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


# `\begin{psmallmatrix}` is amsmath; mitex only knows `smallmatrix`.
PSMALLMATRIX = re.compile(r"\\begin\{psmallmatrix\}(.*?)\\end\{psmallmatrix\}", re.S)
MATH_REF_WITH_PREFIX = re.compile(r"\b(Theorem|Lemma|Proposition|Corollary|Definition|Remark|Section)~\\ref\{([^}]*)\}")
MATH_REF = re.compile(r"\\ref\{([^}]*)\}")


def normalize_math(src: str, resolve_ref: Callable[[str, str | None], str]) -> str:
    """Rewrite LaTeX math into what ``mitex`` accepts.

    * ``\\ref`` is replaced by its resolved text (``resolve_ref(label, prefix)``), since
      mitex would turn it into a Typst reference that does not exist here.
    * ``psmallmatrix`` becomes parentheses around ``smallmatrix``.
    """
    def ref_text(label: str, prefix: str | None) -> str:
        return resolve_ref(label, prefix).replace("#", "\\#")

    src = MATH_REF_WITH_PREFIX.sub(lambda m: ref_text(m.group(2), m.group(1)), src)
    src = MATH_REF.sub(lambda m: ref_text(m.group(1), None), src)
    src = PSMALLMATRIX.sub(r"\\left(\\begin{smallmatrix}\1\\end{smallmatrix}\\right)", src)
    if "`" in src:
        raise ConversionError(f"backtick in math cannot be passed to mitex: {src[:60]!r}")
    return src
