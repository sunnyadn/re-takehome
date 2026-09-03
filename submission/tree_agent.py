"""The proof tree wired to Lean: a challenge becomes trees, a block at a leaf
becomes a rendered file, one check, and the printed goals flow back to the
leaves. The search loop on top of this is the next slice."""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from submission.board_agent import read_board
from submission.framework import DECL_HEAD, placeholders
from submission.proof_tree import GoalNode, ProofTree

SORRY_DECL = re.compile(r"(?P<head>^(?:theorem|lemma)\b.*?:=[ \t]*by)[ \t]*\n(?P<indent>[ \t]+)sorry[ \t]*\n",
                        re.M | re.S)


@dataclass
class Forest:
    """The file as prefix text, one tree per declaration left as `sorry`, and
    the text between them. `render()` is the whole file."""

    parts: list[str | ProofTree] = field(default_factory=list)

    @property
    def trees(self) -> list[ProofTree]:
        return [p for p in self.parts if isinstance(p, ProofTree)]

    def render(self) -> str:
        return "".join(p if isinstance(p, str) else p.render() for p in self.parts)

    def leaves(self) -> list[GoalNode]:
        return [g for t in self.trees for g in t.leaves()]


def forest_from_challenge(challenge: str) -> Forest:
    """Every `theorem … := by\\n  sorry` becomes a tree whose header is the
    declaration line(s); everything else is kept verbatim."""

    out, pos = Forest(), 0
    for m in SORRY_DECL.finditer(challenge):
        out.parts.append(challenge[pos:m.start()])
        out.parts.append(ProofTree(m.group("head") + "\n", "", indent=m.group("indent")))
        pos = m.end()
    out.parts.append(challenge[pos:])
    return out


def observe(forest: Forest, messages, accepted: bool) -> None:
    """Lean's printed goals for the rendered file, mapped to the leaves in
    file order (the board reader already pairs each placeholder with the
    tightest `unsolved goals` span holding it)."""

    board = read_board(forest.render(), messages, accepted)
    texts = [g.text for g in board.goals]
    leaves = forest.leaves()
    if len(texts) != len(leaves):
        raise ValueError(f"{len(texts)} placeholders read for {len(leaves)} leaves")
    for leaf, text in zip(leaves, texts):
        leaf.text = text
