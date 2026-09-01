"""Replay proofs Lean has already accepted through the cursor machinery.

The corpus lives outside the repo; set FRAMEWORK_PROOFS to a directory of
accepted .lean files to run this.
"""

from __future__ import annotations

import os
from pathlib import Path

import pytest

from submission import framework as fw

CORPUS = os.environ.get(
    "FRAMEWORK_PROOFS",
    str(Path.home() / "Projects/ai-contribution/re-takehome-runs/mathwork/follow16"),
)
pytestmark = pytest.mark.skipif(
    not Path(CORPUS).is_dir(), reason="set FRAMEWORK_PROOFS to a directory of proofs")


def bodies(text: str) -> list[tuple[str, list[str]]]:
    """Each declaration's tactic block. A statement may run over several lines."""

    lines, out, i = text.split("\n"), [], 0
    while i < len(lines):
        if lines[i].rstrip().endswith(":= by"):
            j = i + 1
            while j < len(lines) and (not lines[j].strip() or lines[j].startswith(" ")):
                j += 1
            block = lines[i + 1: j]
            while block and not block[-1].strip():
                block.pop()
            out.append((lines[i], block))
            i = j
        else:
            i += 1
    return out


def steps(block: list[str]) -> list[str]:
    """A line at the base indent starts a step; deeper lines belong to it."""

    base = min(len(l) - len(l.lstrip()) for l in block if l.strip())
    out: list[list[str]] = []
    for line in block:
        if line.strip() and len(line) - len(line.lstrip()) == base:
            out.append([line])
        elif out:
            out[-1].append(line)
    return ["\n".join(s).rstrip() for s in out]


def test_every_accepted_proof_replays_byte_for_byte():
    seen = 0
    for path in sorted(Path(CORPUS).glob("*.lean")):
        for head, block in bodies(path.read_text()):
            seen += 1
            text = head + "\n  sorry\n"
            for step in steps(block):
                text, _ = fw.replace_cursor(text, step)
            left = fw.cursor(text)
            if left:
                text = fw.drop_lines(text, [fw.line_of(text, left.start())])
            got = "\n".join(text.split("\n")[1:]).rstrip()
            assert got == "\n".join(block).rstrip(), f"{path.name}: {head[:60]}"
    assert seen >= 16
