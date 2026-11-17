"""Several blueprint chapters as one book.

Every chapter file is parsed on its own (``parser.parse_file``); ``merge_chapters`` joins them.
Sections continue across chapters (the first section of chapter 2 is book section 16 when chapter 1
has 15), and a later chapter's title and introduction open its first section, so that each
chapter still starts on a page of its own and no extra kind of book section is needed.
"""
from __future__ import annotations

from .errors import ConversionError
from .model import Document, Heading


def chapter_heading(document: Document) -> Heading:
    return Heading(0, document.title, document.label)


def merge_chapters(documents: list[Document]) -> Document:
    """One document: the first chapter's introduction, then the sections of all chapters."""
    if not documents:
        raise ConversionError("no chapter given")
    first = documents[0]
    merged = Document(first.title, first.label, front=[chapter_heading(first), *first.front])
    for number, chapter in enumerate(documents, start=1):
        sections = [list(blocks) for blocks in chapter.sections]
        if number > 1:
            if not sections:
                raise ConversionError(f"chapter {number} ({chapter.label}) has no \\section")
            sections[0] = [chapter_heading(chapter), *chapter.front, *sections[0]]
        merged.sections.extend(sections)
    return merged
