"""AST -> Typst markup.

The generated markup relies on the functions of ``theme.typ`` (``thm``, ``proof``, ``rf``,
``tt``, ``run-in``, ``labeled-items``) and on ``mi`` / ``mitex`` for math.
"""
from __future__ import annotations

from .errors import ConversionError
from .index import Index
from .model import (Block, DisplayMath, Environment, Heading, Inline, LineBreak, ListBlock,
                    Math, Paragraph, Proof, Ref, RunInHead, Styled, Text)
from .text import escape_line_start, escape_markup, normalize_math, typst_string

STYLE_FUNCTION = {"emph": "emph", "strong": "strong", "mono": "tt"}


class Emitter:
    """Turns the blocks of one book section into Typst source."""

    def __init__(self, index: Index, part: int):
        self.index = index
        self.part = part

    # ------------------------------------------------------------------ inline
    def inlines(self, nodes: list[Inline]) -> str:
        return "".join(self.inline(n) for n in nodes)

    def inline(self, node: Inline) -> str:
        # Every call ends in `;` so that following text such as `.` or `(` is not read
        # by Typst as field access or a further call argument.
        if isinstance(node, Text):
            return escape_markup(node.value)
        if isinstance(node, Math):
            return f"#mi(`{self.math(node.src)}`);"
        if isinstance(node, Styled):
            return f"#{STYLE_FUNCTION[node.style]}[{self.inlines(node.children)}];"
        if isinstance(node, Ref):
            return self.ref(node)
        if isinstance(node, LineBreak):
            return "#linebreak();"
        raise ConversionError(f"unexpected inline node {node!r}")

    def math(self, src: str) -> str:
        return normalize_math(src, self.index.ref_text)

    def ref(self, node: Ref) -> str:
        text = self.index.ref_text(node.label, node.prefix)
        arguments = [typst_string(node.label), typst_string(text)]
        info = self.index.labels.get(node.label)
        if info is None:
            arguments.append("external: true")
        elif info.part != self.part:
            arguments.append(typst_string(f"s{info.part:02d}").join(["section: ", ""]))
        return f"#rf({', '.join(arguments)});"

    def line(self, nodes: list[Inline]) -> str:
        """Inline content on one line, safe at the start of a paragraph."""
        return escape_line_start(self.inlines(nodes).strip())

    # ------------------------------------------------------------------ blocks
    def blocks(self, blocks: list[Block]) -> str:
        parts: list[str] = []
        i = 0
        while i < len(blocks):
            block = blocks[i]
            if isinstance(block, RunInHead) and i + 1 < len(blocks) and isinstance(blocks[i + 1], Paragraph):
                head = f"#run-in[{self.inlines(block.inlines)}]; "
                parts.append(head + self.line(blocks[i + 1].inlines))
                i += 2
                continue
            parts.append(self.block(block))
            i += 1
        return "\n\n".join(p for p in parts if p)

    def block(self, block: Block) -> str:
        if isinstance(block, Paragraph):
            return self.line(block.inlines)
        if isinstance(block, DisplayMath):
            return f"#mitex(`{self.math(block.src)}`)"
        if isinstance(block, RunInHead):
            return f"#run-in[{self.inlines(block.inlines)}];"
        if isinstance(block, ListBlock):
            return self.list_block(block)
        if isinstance(block, Heading):
            return self.heading(block)
        if isinstance(block, Environment):
            return self.environment(block)
        if isinstance(block, Proof):
            return f"#proof[\n{self.blocks(block.blocks)}\n]"
        raise ConversionError(f"unexpected block {block!r}")

    def heading(self, heading: Heading) -> str:
        label = f" <{heading.label}>" if heading.label else ""
        return f"{'=' * heading.level} {self.inlines(heading.title).strip()}{label}"

    def list_block(self, block: ListBlock) -> str:
        if any(item.marker for item in block.items):
            if not all(item.marker for item in block.items):
                raise ConversionError("a list mixes \\item and \\item[marker]")
            entries = [f"([{self.inlines(i.marker)}], [\n{self.blocks(i.blocks)}\n])" for i in block.items]
            return "#labeled-items(\n" + ",\n".join(entries) + ",\n)"
        function = "enum" if block.ordered else "list"
        entries = [f"[\n{self.blocks(i.blocks)}\n]" for i in block.items]
        return f"#{function}(tight: false,\n" + ",\n".join(entries) + ",\n)"

    def environment(self, env: Environment) -> str:
        info = self.index.labels.get(env.label) if env.label else None
        serial = self.index.serials[id(env)]
        arguments = [typst_string(env.kind), str(serial)]
        if info and info.tal_number:
            arguments.append(f"tal: ({typst_string(info.tal_kind)}, {typst_string(info.tal_number)})")
        if env.title:
            arguments.append(f"title: [{self.inlines(env.title)}]")
        if env.label:
            arguments.append(f"label: {typst_string(env.label)}")
        if env.source:
            arguments.append(f"source: [{self.inlines(env.source)}]")
        if env.lean:
            names = ", ".join(typst_string(n) for n in env.lean)
            arguments.append(f"names: ({names},)")
        return f"#thm({', '.join(arguments)})[\n{self.blocks(env.blocks)}\n]"
