"""Locating the sample inputs of the checks, with a clear failure when one is missing."""
import subprocess
from pathlib import Path

SAMPLES_DIR = Path(__file__).parent / "samples"
MINI_TEX = SAMPLES_DIR / "mini.tex"


def git_ignore_rule(path: Path) -> str | None:
    """The `.gitignore` rule that hides ``path`` (``file:line:pattern``), or None.

    Also None when git is unavailable or ``path`` is not in a repository.
    """
    try:
        result = subprocess.run(
            ["git", "check-ignore", "-v", str(path)],
            cwd=path.parent, capture_output=True, text=True, check=False)
    except OSError:
        return None
    if result.returncode != 0:
        return None
    return result.stdout.split("\t")[0]


def read_sample(path: Path = MINI_TEX) -> str:
    """Read a sample input; explain *why* it may be missing instead of a bare traceback."""
    if path.exists():
        return path.read_text(encoding="utf-8")
    rule = git_ignore_rule(path)
    hint = (f"; its location matches the .gitignore rule {rule}, so it is probably not committed"
            if rule else "")
    raise FileNotFoundError(f"check input {path} does not exist{hint}")
