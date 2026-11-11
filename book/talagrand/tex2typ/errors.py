"""Error type shared by all conversion stages."""


class ConversionError(Exception):
    """The LaTeX source uses something this converter does not handle."""

    def __init__(self, message: str, source: str = "", offset: int = 0, filename: str = "<tex>"):
        line = source.count("\n", 0, offset) + 1 if source else 0
        where = f"{filename}:{line}: " if line else ""
        super().__init__(where + message)
