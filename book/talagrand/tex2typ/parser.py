"""LaTeX -> AST for the blueprint subset (see ``model``).

The parser works on one source string and passes ``(lo, hi)`` windows around, so every
error can report the line of the original file.
"""
from __future__ import annotations

import re
import unicodedata
from typing import Iterator

from .errors import ConversionError
from .model import (Block, DisplayMath, Document, Environment, Heading, Inline, LineBreak,
                    ListBlock, ListItem, Math, Meta, Paragraph, Proof, Ref, RunInHead, Styled, Text)
from .scanner import find_matching_end, read_group, read_optional, skip_space

NBSP = "\u00a0"
THEOREM_KINDS = {"theorem", "lemma", "proposition", "corollary", "definition", "remark"}
HEADING_LEVELS = {"chapter": 0, "section": 1, "subsection": 2, "subsubsection": 3}
STYLES = {"emph": "emph", "textit": "emph", "textbf": "strong", "texttt": "mono"}
IGNORED_COMMANDS = {"medskip", "smallskip", "bigskip", "noindent", "newpage", "clearpage"}
FLAG_COMMANDS = {"leanok", "notready", "mathlibok"}
# Commands whose single argument is a comma separated list of names or labels.
LIST_COMMANDS = {"lean", "uses"}
ACCENTS = {'"': "\u0308", "'": "\u0301", "`": "\u0300", "^": "\u0302", "~": "\u0303",
           "H": "\u030b", "c": "\u0327", "v": "\u030c"}
LETTER_SYMBOLS = {"l": "ł", "L": "Ł", "o": "ø", "O": "Ø", "ss": "ß", "dots": "…", "ldots": "…"}
ESCAPED_CHARACTERS = set("_{}%&#$")
SPACING = {" ": " ", ",": "\u2009", ";": " ", ":": " ", "-": "", "/": ""}
REF_PREFIX = re.compile(r"\b(Theorem|Lemma|Proposition|Corollary|Definition|Remark|Section)" + NBSP + r"$")

# Tokens that end a run of plain text: math (to be skipped over), environments, headings.
BLOCK_TOKEN = re.compile(r"""
    (?P<dollar2>(?<!\\)\$\$)
  | (?P<dollar>(?<!\\)\$)
  | (?P<bracket>(?<!\\)\\\[)
  | (?P<begin>\\begin\{(?P<env>[A-Za-z*]+)\})
  | (?P<heading>\\(?P<hkind>chapter|section|subsection|subsubsection)\*?\s*\{)
  | (?P<para>\\paragraph\s*\{)
""", re.X)
BLANK_LINE = re.compile(r"\n[ \t]*\n")
LIST_TOKEN = re.compile(r"\\item\b|\\begin\{(?:itemize|enumerate)\}|\\end\{(?:itemize|enumerate)\}")
COMMENT = re.compile(r"(?<!\\)%[^\n]*")


def strip_comments(text: str) -> str:
    """Blank out ``%`` comments, keeping offsets (and so line numbers) unchanged."""
    return COMMENT.sub(lambda m: " " * len(m.group()), text)


class Parser:
    def __init__(self, text: str, filename: str = "<tex>"):
        self.text = strip_comments(text)
        self.filename = filename

    # ------------------------------------------------------------------ helpers
    def error(self, message: str, offset: int) -> ConversionError:
        return ConversionError(message, self.text, offset, self.filename)

    def group(self, pos: int) -> tuple[int, int, int]:
        return read_group(self.text, pos, self.filename)

    def closing_dollar(self, start: int, double: bool) -> int:
        """Index of the ``$`` (or ``$$``) closing the math that starts at ``start``."""
        needle = "$$" if double else "$"
        i = start
        while True:
            i = self.text.find(needle, i)
            if i < 0:
                raise self.error("unterminated math", start)
            if self.text[i - 1] == "\\" and self.text[i - 2] != "\\":
                i += 1
                continue
            return i

    # ------------------------------------------------------------------- inline
    def parse_inline(self, lo: int, hi: int) -> list[Inline]:
        out: list[Inline] = []
        buffer: list[str] = []

        def flush_text() -> None:
            if buffer:
                out.append(Text(self.typographic("".join(buffer))))
                buffer.clear()

        pos = lo
        while pos < hi:
            c = self.text[pos]
            if c == "$":
                double = self.text.startswith("$$", pos)
                skip = 2 if double else 1
                end = self.closing_dollar(pos + skip, double)
                flush_text()
                if double:
                    raise self.error("display math ($$) inside running text", pos)
                out.append(Math(self.text[pos + 1:end].strip()))
                pos = end + 1
            elif c == "\\":
                pos = self.parse_command(pos, hi, out, buffer, flush_text)
            elif c == "~":
                buffer.append(NBSP)
                pos += 1
            elif c in "{}":
                pos += 1  # plain TeX grouping has no visible effect here
            else:
                buffer.append(c)
                pos += 1
        flush_text()
        return out

    @staticmethod
    def typographic(text: str) -> str:
        """TeX quotes: ``quoted'' -> “quoted”."""
        return text.replace("``", "\u201c").replace("''", "\u201d").replace("`", "\u2018")

    def parse_command(self, pos: int, hi: int, out: list[Inline], buffer: list[str], flush_text) -> int:
        """Handle the command at ``text[pos] == '\\'``; return the next position."""
        m = re.compile(r"\\([A-Za-z]+)").match(self.text, pos)
        if not m:  # control symbol such as \\ \_ \" \,
            return self.parse_control_symbol(pos, hi, out, buffer, flush_text)
        name = m.group(1)
        after = m.end()
        if name in STYLES or name == "text":
            lo_, hi_, after = self.group(skip_space(self.text, after))
            children = self.parse_inline(lo_, hi_)
            flush_text()
            if name == "text":
                out.extend(children)
            else:
                out.append(Styled(STYLES[name], children))
            return after
        if name == "ref":
            lo_, hi_, after = self.group(after)
            prefix_match = REF_PREFIX.search("".join(buffer))
            prefix = None
            if prefix_match:
                prefix = prefix_match.group(1)
                kept = "".join(buffer)[:prefix_match.start()]
                buffer.clear()
                buffer.append(kept)
            flush_text()
            out.append(Ref(self.text[lo_:hi_].strip(), prefix))
            return after
        if name == "label":
            lo_, hi_, after = self.group(after)
            flush_text()
            out.append(Meta("label", self.text[lo_:hi_].strip()))
            return after
        if name in LIST_COMMANDS:
            lo_, hi_, after = self.group(skip_space(self.text, after))
            names = [n.strip() for n in self.text[lo_:hi_].split(",") if n.strip()]
            flush_text()
            out.append(Meta(name, names))
            return after
        if name == "talsource":
            lo_, hi_, after = self.group(after)
            flush_text()
            out.append(Meta("talsource", self.parse_inline(lo_, hi_)))
            return after
        if name in FLAG_COMMANDS:
            flush_text()
            out.append(Meta("flag", name))
            return after
        if name in IGNORED_COMMANDS:
            return after
        if name in LETTER_SYMBOLS:
            buffer.append(LETTER_SYMBOLS[name])
            if self.text.startswith("{}", after):
                after += 2  # `Lata\l{}a`: the empty group only terminates the command
            return after
        if name in ACCENTS:
            return self.parse_accent(ACCENTS[name], skip_space(self.text, after), buffer)
        raise self.error(f"unsupported command \\{name}", pos)

    def parse_control_symbol(self, pos: int, hi: int, out: list[Inline], buffer: list[str], flush_text) -> int:
        if pos + 1 >= hi:
            raise self.error("dangling backslash", pos)
        c = self.text[pos + 1]
        if c == "\\":
            flush_text()
            out.append(LineBreak())
            return pos + 2
        if c in ESCAPED_CHARACTERS:
            buffer.append(c)
            return pos + 2
        if c in SPACING:
            buffer.append(SPACING[c])
            return pos + 2
        if c in ACCENTS:
            return self.parse_accent(ACCENTS[c], pos + 2, buffer)
        raise self.error(f"unsupported control symbol \\{c}", pos)

    def parse_accent(self, combining: str, pos: int, buffer: list[str]) -> int:
        """``\\"o`` or ``\\"{o}``: append the composed character."""
        if self.text[pos] == "{":
            lo, hi, after = self.group(pos)
            letter = self.text[lo:hi]
        else:
            letter, after = self.text[pos], pos + 1
        buffer.append(unicodedata.normalize("NFC", letter + combining))
        return after

    # ------------------------------------------------------------------- blocks
    def parse_blocks(self, lo: int, hi: int) -> list[Block]:
        blocks: list[Block] = []
        flush_from = pos = lo
        while True:
            m = BLOCK_TOKEN.search(self.text, pos, hi)
            if m is None:
                break
            if m.group("dollar"):  # inline math: part of the running text, skip over it
                pos = self.closing_dollar(m.end(), False) + 1
                continue
            blocks.extend(self.paragraphs(flush_from, m.start()))
            if m.group("dollar2"):
                end = self.closing_dollar(m.end(), True)
                blocks.append(DisplayMath(self.text[m.end():end].strip()))
                pos = end + 2
            elif m.group("bracket"):
                end = self.text.find("\\]", m.end())
                if end < 0 or end > hi:
                    raise self.error("unterminated \\[", m.start())
                blocks.append(DisplayMath(self.text[m.end():end].strip()))
                pos = end + 2
            elif m.group("begin"):
                block, pos = self.parse_environment(m, hi)
                blocks.append(block)
            elif m.group("heading"):
                block, pos = self.parse_heading(m)
                blocks.append(block)
            else:  # \paragraph{...}
                lo_, hi_, pos = self.group(m.end() - 1)
                blocks.append(RunInHead(self.parse_inline(lo_, hi_)))
            flush_from = pos
        blocks.extend(self.paragraphs(flush_from, hi))
        return blocks

    def paragraphs(self, lo: int, hi: int) -> Iterator[Paragraph]:
        """Running text between block tokens, split at blank lines."""
        start = lo
        for blank in list(BLANK_LINE.finditer(self.text, lo, hi)) + [None]:
            end = hi if blank is None else blank.start()
            if self.text[start:end].strip():
                yield Paragraph(self.parse_inline(start, end))
            if blank is not None:
                start = blank.end()

    def parse_heading(self, m: re.Match) -> tuple[Heading, int]:
        lo, hi, pos = self.group(m.end() - 1)
        title = self.parse_inline(lo, hi)
        label = None
        probe = skip_space(self.text, pos)
        if self.text.startswith("\\label", probe):
            lo, hi, pos = self.group(probe + len("\\label"))
            label = self.text[lo:hi].strip()
        return Heading(HEADING_LEVELS[m.group("hkind")], title, label), pos

    def parse_environment(self, m: re.Match, hi: int) -> tuple[Block, int]:
        name = m.group("env")
        body_lo = m.end()
        end = find_matching_end(self.text, name, body_lo, self.filename)
        after = end + len(f"\\end{{{name}}}")
        if name in THEOREM_KINDS:
            title = None
            optional = read_optional(self.text, body_lo, self.filename)
            if optional:
                title = self.parse_inline(optional[0], optional[1])
                body_lo = optional[2]
            return self.make_environment(name, title, self.parse_blocks(body_lo, end)), after
        if name == "proof":
            blocks = self.parse_blocks(body_lo, end)
            harvest_meta(blocks)  # \leanok / \uses carry nothing for the book
            return Proof(blocks), after
        if name in {"itemize", "enumerate"}:
            return ListBlock(name == "enumerate", self.parse_items(body_lo, end)), after
        if name == "align*":
            return DisplayMath(self.text[m.start():after].strip()), after
        raise self.error(f"unsupported environment {name}", m.start())

    def parse_items(self, lo: int, hi: int) -> list[ListItem]:
        """Split a list body at its own ``\\item`` tokens (nested lists are skipped)."""
        starts: list[int] = []
        depth = 0
        for m in LIST_TOKEN.finditer(self.text, lo, hi):
            if m.group().startswith("\\begin"):
                depth += 1
            elif m.group().startswith("\\end"):
                depth -= 1
            elif depth == 0:
                starts.append(m.start())
        if not starts or self.text[lo:starts[0]].strip():
            raise self.error("list body must start with \\item", lo)
        items = []
        for index, start in enumerate(starts):
            stop = starts[index + 1] if index + 1 < len(starts) else hi
            body_lo = start + len("\\item")
            marker = None
            optional = read_optional(self.text, skip_space(self.text, body_lo), self.filename)
            if optional:
                marker = self.parse_inline(optional[0], optional[1])
                body_lo = optional[2]
            items.append(ListItem(marker, self.parse_blocks(body_lo, stop)))
        return items

    def make_environment(self, kind: str, title: list[Inline] | None, blocks: list[Block]) -> Environment:
        meta = harvest_meta(blocks)
        return Environment(kind, title, meta.get("label"), meta.get("lean", []),
                           meta.get("talsource"), blocks)

    # ----------------------------------------------------------------- document
    def parse_document(self) -> Document:
        blocks = self.parse_blocks(0, len(self.text))
        chapters = [b for b in blocks if isinstance(b, Heading) and b.level == 0]
        if len(chapters) != 1 or blocks[0] is not chapters[0]:
            raise ConversionError("expected exactly one \\chapter at the start", self.text, 0, self.filename)
        document = Document(chapters[0].title, chapters[0].label)
        current = document.front
        for block in blocks[1:]:
            if isinstance(block, Heading) and block.level == 1:
                current = []
                document.sections.append(current)
            current.append(block)
        return document


def harvest_meta(blocks: list[Block]) -> dict:
    """Remove ``Meta`` inline nodes from the top-level paragraphs and return their values.

    Paragraphs left empty (they only held ``\\label``/``\\lean``/... commands) are dropped.
    """
    found: dict = {}
    for block in list(blocks):
        if not isinstance(block, Paragraph):
            continue
        kept = []
        for node in block.inlines:
            if not isinstance(node, Meta):
                kept.append(node)
            elif node.kind == "lean":
                found.setdefault("lean", []).extend(node.value)
            elif node.kind in {"label", "talsource"}:
                found[node.kind] = node.value
        block.inlines = kept
        if all(isinstance(n, Text) and not n.value.strip() for n in kept):
            blocks.remove(block)
    return found


def parse_file(path) -> Document:
    from pathlib import Path
    path = Path(path)
    return Parser(path.read_text(encoding="utf-8"), str(path)).parse_document()
