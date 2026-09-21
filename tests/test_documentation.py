"""Guards for the two documentation invariants the README states.

Neither test touches the numerics; they exist because both invariants are easy
to break silently -- a label renamed in the paper, or a module renamed here --
and the README promises they hold.
"""

from __future__ import annotations

import importlib
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"

# The prefixes the paper uses for its \label commands.
LABEL = re.compile(
    r"``((?:app|cor|def|eq|ex|item|lem|prop|rmk|sec|subsec|thm):[A-Za-z0-9_:-]+)``"
)


def _python_sources() -> list[Path]:
    return sorted((ROOT / "src").rglob("*.py")) + sorted((ROOT / "experiments").rglob("*.py"))


def test_docstring_cross_references_exist_in_the_paper():
    """``thm:...``, ``eq:...`` in a docstring must name a real ``\\label``."""
    sections = sorted(PAPER.rglob("*.tex"))
    if not sections:
        pytest.skip("the paper submodule is not checked out")

    labels = set()
    for tex in sections:
        labels |= set(re.findall(r"\\label\{([^}]*)\}", tex.read_text(errors="replace")))

    dangling: dict[str, set[str]] = {}
    for source in _python_sources():
        for ref in LABEL.findall(source.read_text()):
            if ref not in labels:
                dangling.setdefault(ref, set()).add(str(source.relative_to(ROOT)))
    assert not dangling, f"cross-references with no \\label in paper/: {dangling}"


def test_readme_module_references_resolve():
    """Every ``ddinf.x.y`` named in the README must still be importable."""
    readme = (ROOT / "README.md").read_text()
    broken = []
    for ref in sorted(set(re.findall(r"`(ddinf\.[A-Za-z_][A-Za-z0-9_.]*)`", readme))):
        parts = ref.split(".")
        for cut in range(len(parts), 1, -1):
            try:
                obj = importlib.import_module(".".join(parts[:cut]))
            except ModuleNotFoundError:
                continue
            for attr in parts[cut:]:
                if not hasattr(obj, attr):
                    broken.append(ref)
                    break
                obj = getattr(obj, attr)
            break
        else:
            broken.append(ref)
    assert not broken, f"README names things that no longer exist: {broken}"
