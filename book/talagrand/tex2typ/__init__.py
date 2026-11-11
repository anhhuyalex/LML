"""Convert the Talagrand blueprint chapter (LaTeX) into a Typst book.

Pipeline: ``parser`` (LaTeX -> AST in ``model``) -> ``index`` (labels, numbering)
-> ``emit`` (AST -> Typst) -> ``cli`` (writes the files).  Only the small LaTeX
subset used by the blueprint is supported; anything else raises ``ConversionError``
with a file and line so that new constructs are noticed instead of mistranslated.
"""
