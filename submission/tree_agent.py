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


def split_goals(text: str) -> list[str]:
    """One printed goal per entry: Lean separates the goals of one message
    with a blank line, each starting with `case` or a hypothesis or `⊢`."""

    parts = [p.strip() for p in re.split(r"\n\s*\n", text.strip()) if p.strip()]
    return parts or [""]


def leaf_index(forest: Forest, leaf: GoalNode) -> int:
    return forest.leaves().index(leaf)


async def attempt(forest: Forest, tree: ProofTree, leaf: GoalNode, block: str, lean,
                  timeout_s: float | None = None) -> tuple[bool, list]:
    """Try a block at a leaf: expand with one subgoal per `sorry` line plus one
    for whatever the block leaves open, check the rendering with every
    placeholder as `skip`, and settle: a placeholder with no goal goes, a
    placeholder holding several goals becomes several leaves. On a real
    failure the expansion is dropped and the messages come back as feedback."""

    from submission.board_agent import render_all
    from submission.framework import classify

    sorries = sum(1 for l in block.split("\n") if l.strip() == "sorry")
    tree.expand(leaf, block, [""] * (sorries + 1))
    for _ in range(4):
        text = forest.render()
        check = await lean.check_file(render_all(text), timeout_s=timeout_s)
        progress, spare, expensive, failures = classify(check.messages)
        if failures or expensive or check.timed_out:
            tree.drop(leaf)
            return False, list(check.messages)
        observe(forest, check.messages, check.accepted)
        node = leaf.tactic
        changed = False
        for sub in list(node.subgoals):
            if sub.tactic is not None:
                continue
            goals = split_goals(sub.text) if sub.text else []
            if not goals:
                node.subgoals.remove(sub)
                changed = True
            elif len(goals) > 1:
                # several goals behind one placeholder: a scaffold node, one
                # case per goal, so each leaf has a placeholder of its own
                tags = [m.group(1) for m in (re.match(r"case (\S+)", g) for g in goals) if m]
                if len(tags) == len(goals):
                    scaffold = "\n".join(f"case {t} =>\n  sorry" for t in tags)
                else:
                    scaffold = "\n".join("· sorry" for _ in goals)
                tree.expand(sub, scaffold, goals)
                changed = True
        if not changed:
            return True, list(check.messages)
    return True, list(check.messages)
