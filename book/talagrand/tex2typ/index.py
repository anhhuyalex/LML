"""Numbering pass: assigns section numbers, box serials and Talagrand numbers to labels."""
from __future__ import annotations

import re
from collections import Counter
from dataclasses import dataclass

from .errors import ConversionError
from .model import Block, Document, Environment, Heading, Inline, Text

TAL_STATEMENT = re.compile(r"\b(Theorem|Lemma|Proposition|Corollary|Definition)s?\u00a0(\d+\.\d+\.\d+)")
# Words used for labels that are defined in other blueprint chapters.
EXTERNAL_KIND = {"thm": "Theorem", "lem": "Lemma", "prop": "Proposition", "cor": "Corollary",
                 "def": "Definition", "rem": "Remark", "sec": "Section", "chap": "Chapter"}


@dataclass
class LabelInfo:
    label: str
    kind: str                 # "section" or a theorem-like kind
    part: int                 # 0 = introduction, 1..n = book sections
    number: str               # section number ("5.2") or box serial ("41")
    tal_kind: str | None = None     # "Lemma" in "Lemma 1.6.3"
    tal_number: str | None = None   # "1.6.3"
    shared: bool = False      # several boxes carry this Talagrand number


def plain_text(inlines: list[Inline]) -> str:
    """Text content of inline nodes (math and references are left out)."""
    return "".join(n.value for n in inlines if isinstance(n, Text))


def talagrand_statement(source: list[Inline] | None) -> tuple[str, str] | None:
    """The first numbered book statement cited by a ``\\talsource`` tag."""
    m = TAL_STATEMENT.search(plain_text(source or []))
    return (m.group(1), m.group(2)) if m else None


class Index:
    """Label table for one document; ``overrides`` maps a label to ``"Kind 1.2.3"`` or ``""``."""

    def __init__(self, document: Document, overrides: dict[str, str] | None = None):
        self.labels: dict[str, LabelInfo] = {}
        self.boxes: dict[int, list[str]] = {}  # part -> labels in order (for reports)
        self.serials: dict[int, int] = {}      # id(Environment) -> serial
        self._overrides = overrides or {}
        self._build(document)
        counts = Counter(i.tal_number for i in self.labels.values() if i.tal_number)
        for info in self.labels.values():
            info.shared = bool(info.tal_number) and counts[info.tal_number] > 1

    # ------------------------------------------------------------------- build
    def _build(self, document: Document) -> None:
        self._serial = 0
        self._walk(document.front, part=0)
        for part, blocks in enumerate(document.sections, start=1):
            # Each section starts with its own level-1 heading, which increments the first counter.
            self._walk(blocks, part, [part - 1, 0, 0])

    def _walk(self, blocks: list[Block], part: int, counters: list[int] | None = None) -> None:
        for block in blocks:
            if isinstance(block, Heading):
                self._heading(block, part, counters)
            elif isinstance(block, Environment):
                self._environment(block, part)

    def _heading(self, heading: Heading, part: int, counters: list[int] | None) -> None:
        if counters is None:
            if heading.label:
                raise ConversionError(f"label {heading.label} on an unnumbered heading")
            return
        level = heading.level
        counters[level - 1] += 1
        for deeper in range(level, 3):
            counters[deeper] = 0
        if heading.label:
            number = ".".join(str(c) for c in counters[:level])
            self._add(LabelInfo(heading.label, "section", part, number))

    def _environment(self, env: Environment, part: int) -> None:
        self._serial += 1
        self.serials[id(env)] = self._serial
        if not env.label:
            return
        tal = talagrand_statement(env.source)
        override = self._overrides.get(env.label)
        if override is not None:
            tal = tuple(override.split(" ", 1)) if override else None
        self._add(LabelInfo(env.label, env.kind, part, str(self._serial),
                            tal[0] if tal else None, tal[1] if tal else None))

    def _add(self, info: LabelInfo) -> None:
        if info.label in self.labels:
            raise ConversionError(f"duplicate label {info.label}")
        self.labels[info.label] = info

    # ------------------------------------------------------------------ queries
    def ref_text(self, label: str, prefix: str | None = None) -> str:
        """Text shown for ``\\ref{label}``: Talagrand's number first (decision 7 of the plan).

        With a ``prefix`` ("Lemma~\\ref{x}") the kind word is part of the result, taken from
        Talagrand's statement when there is one so that it never contradicts the book.
        """
        info = self.labels.get(label)
        nbsp = "\u00a0"
        if info is None:
            kind = EXTERNAL_KIND.get(label.split(":", 1)[0], "")
            return f"{kind}{nbsp if kind else ''}[{label}]"
        if info.kind == "section":
            return f"{prefix + nbsp if prefix else ''}{info.number}"
        if info.tal_number:
            text = info.tal_number + (f" [#{info.number}]" if info.shared else "")
            return f"{info.tal_kind}{nbsp}{text}" if prefix else text
        return f"{info.kind.capitalize()}{nbsp}{info.number}" if prefix else info.number

    def is_external(self, label: str) -> bool:
        return label not in self.labels
