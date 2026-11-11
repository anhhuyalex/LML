"""Low-level helpers for reading LaTeX source: brace groups, optional arguments."""
from __future__ import annotations

from .errors import ConversionError


def read_group(text: str, pos: int, filename: str = "<tex>") -> tuple[int, int, int]:
    """Read the ``{...}`` group that starts at ``text[pos]``.

    Returns ``(inner_start, inner_end, after)``.  Escaped braces (``\\{``) do not count.
    """
    if pos >= len(text) or text[pos] != "{":
        raise ConversionError("expected '{'", text, pos, filename)
    depth = 0
    i = pos
    while i < len(text):
        c = text[i]
        if c == "\\":
            i += 2
            continue
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return pos + 1, i, i + 1
        i += 1
    raise ConversionError("unbalanced '{'", text, pos, filename)


def skip_space(text: str, pos: int) -> int:
    while pos < len(text) and text[pos].isspace():
        pos += 1
    return pos


def read_optional(text: str, pos: int, filename: str = "<tex>") -> tuple[int, int, int] | None:
    """Read an optional ``[...]`` argument at ``pos`` (no leading whitespace allowed).

    Brackets inside braces or inline math (``$[0,1]$``) do not close the argument.
    """
    if pos >= len(text) or text[pos] != "[":
        return None
    depth_bracket = depth_brace = 0
    in_math = False
    i = pos
    while i < len(text):
        c = text[i]
        if c == "\\":
            i += 2
            continue
        if c == "$":
            in_math = not in_math
        elif not in_math:
            if c == "{":
                depth_brace += 1
            elif c == "}":
                depth_brace -= 1
            elif depth_brace == 0 and c == "[":
                depth_bracket += 1
            elif depth_brace == 0 and c == "]":
                depth_bracket -= 1
                if depth_bracket == 0:
                    return pos + 1, i, i + 1
        i += 1
    raise ConversionError("unbalanced '['", text, pos, filename)


def find_matching_end(text: str, name: str, start: int, filename: str = "<tex>") -> int:
    """Position of the ``\\end{name}`` that closes a ``\\begin{name}`` ending at ``start``."""
    begin, end = f"\\begin{{{name}}}", f"\\end{{{name}}}"
    depth = 1
    i = start
    while True:
        next_begin = text.find(begin, i)
        next_end = text.find(end, i)
        if next_end < 0:
            raise ConversionError(f"missing \\end{{{name}}}", text, start, filename)
        if 0 <= next_begin < next_end:
            depth += 1
            i = next_begin + len(begin)
        else:
            depth -= 1
            if depth == 0:
                return next_end
            i = next_end + len(end)
