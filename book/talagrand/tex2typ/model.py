"""Typed syntax tree for the LaTeX subset used by the blueprint chapter."""
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Union


# ---------------------------------------------------------------- inline nodes
@dataclass(frozen=True)
class Text:
    value: str


@dataclass(frozen=True)
class Math:
    """Inline math; ``src`` is LaTeX math without the dollar signs."""
    src: str


@dataclass(frozen=True)
class Styled:
    """``\\emph``, ``\\textbf`` or ``\\texttt`` around inline content."""
    style: str  # "emph" | "strong" | "mono"
    children: list["Inline"]


@dataclass(frozen=True)
class Ref:
    """``\\ref{label}``; ``prefix`` is the word written right before it ("Lemma~")."""
    label: str
    prefix: str | None = None


@dataclass(frozen=True)
class LineBreak:
    pass


@dataclass(frozen=True)
class Meta:
    """Blueprint bookkeeping (``\\label``, ``\\lean`` ...), removed by the parser."""
    kind: str  # "label" | "lean" | "uses" | "talsource" | "flag"
    value: Union[str, list["Inline"], list[str], None] = None


Inline = Union[Text, Math, Styled, Ref, LineBreak, Meta]


# ---------------------------------------------------------------- block nodes
@dataclass
class Paragraph:
    inlines: list[Inline]


@dataclass
class DisplayMath:
    src: str


@dataclass
class RunInHead:
    """``\\paragraph{...}``: a bold run-in heading."""
    inlines: list[Inline]


@dataclass
class ListItem:
    marker: list[Inline] | None  # from ``\\item[marker]``
    blocks: list["Block"]


@dataclass
class ListBlock:
    ordered: bool
    items: list[ListItem]


@dataclass
class Heading:
    level: int  # 0 chapter, 1 section, 2 subsection, 3 subsubsection
    title: list[Inline]
    label: str | None = None


@dataclass
class Environment:
    """A theorem-like environment together with its blueprint metadata."""
    kind: str  # theorem | lemma | proposition | corollary | definition | remark
    title: list[Inline] | None
    label: str | None
    lean: list[str]
    source: list[Inline] | None  # the ``\\talsource`` text
    blocks: list["Block"]


@dataclass
class Proof:
    blocks: list["Block"]


Block = Union[Paragraph, DisplayMath, RunInHead, ListBlock, Heading, Environment, Proof]


@dataclass
class Document:
    """Everything before the first ``\\section`` is ``front``; then one list per section."""
    title: list[Inline]
    label: str | None
    front: list[Block] = field(default_factory=list)
    sections: list[list[Block]] = field(default_factory=list)  # each starts with its Heading
