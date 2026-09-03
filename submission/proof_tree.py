"""A proof as a tree: goal nodes and tactic nodes alternate. The Lean file is
a rendering of the tree; every undo is `drop` at one goal, whatever its depth."""

from __future__ import annotations

from dataclasses import dataclass, field

PLACEHOLDER = "sorry"


@dataclass(eq=False)
class GoalNode:
    """One open or closed goal. `text` is what Lean last printed for it; the
    node, not the text, is its identity."""

    text: str
    parent: "TacticNode | None" = None
    tactic: "TacticNode | None" = None
    tries: int = 0
    swept: bool = False
    history: list[str] = field(default_factory=list)

    def parent_goal(self) -> "GoalNode | None":
        """The goal whose block produced this one; a scaffold is not a choice
        anyone made, so it does not count as a level."""
        node = self.parent
        while node is not None and node.scaffold:
            node = node.goal.parent
        return node.goal if node else None


@dataclass(eq=False)
class TacticNode:
    """A block of tactic lines applied at `goal`; its `sorry` lines, in order,
    are the subgoals it left open."""

    goal: GoalNode
    block: str
    subgoals: list[GoalNode] = field(default_factory=list)
    scaffold: bool = False   # written by the harness to give each goal a placeholder


class ProofTree:
    def __init__(self, header: str, root_text: str, indent: str = "  ") -> None:
        self.header, self.indent = header, indent
        self.root = GoalNode(root_text)

    def expand(self, goal: GoalNode, block: str, subgoal_texts: list[str]) -> list[GoalNode]:
        """Attach a block at an open goal. One subgoal per `sorry` line in the
        block, in order, carrying the texts Lean printed for them."""

        assert goal.tactic is None, "goal already has a tactic; drop it first"
        node = TacticNode(goal, block.rstrip("\n"))
        node.subgoals = [GoalNode(t, parent=node) for t in subgoal_texts]
        goal.tactic = node
        return node.subgoals

    def retract(self, goal: GoalNode) -> None:
        """Take the block at this goal back (Lean rejected it); the goal keeps
        its count of attempts."""

        if goal.tactic is not None:
            goal.history.append(goal.tactic.block)
        goal.tactic = None

    def drop(self, goal: GoalNode) -> None:
        """Forget everything under this goal and start it afresh. Its siblings,
        and every proved fact above it, are untouched."""

        self.retract(goal)
        goal.tries, goal.swept = 0, False

    def leaves(self) -> list[GoalNode]:
        out: list[GoalNode] = []

        def walk(g: GoalNode) -> None:
            if g.tactic is None:
                out.append(g)
            else:
                for s in g.tactic.subgoals:
                    walk(s)
        walk(self.root)
        return out

    def observe(self, printed: list[str]) -> None:
        """Lean printed the open goals of the rendered file, in file order:
        the same order as the leaves. Texts refresh, identities stay."""

        leaves = self.leaves()
        if len(printed) != len(leaves):
            raise ValueError(f"{len(printed)} goals printed for {len(leaves)} leaves")
        for leaf, text in zip(leaves, printed):
            leaf.text = text

    def render(self) -> str:
        return self.header + self._render(self.root, self.indent)

    def _render(self, goal: GoalNode, indent: str) -> str:
        if goal.tactic is None:
            return f"{indent}{PLACEHOLDER}\n"
        lines, subs, out = goal.tactic.block.split("\n"), list(goal.tactic.subgoals), []
        for line in lines:
            body = line.strip()
            lead = line[:len(line) - len(line.lstrip())]
            if body == PLACEHOLDER and subs:
                out.append(self._render(subs.pop(0), indent + lead))
            else:
                out.append(f"{indent}{line}\n")
        # goals the block left open without writing a placeholder for them
        # (`constructor`, `rcases`) follow it, at its own indent
        for sub in subs:
            out.append(self._render(sub, indent))
        return "".join(out)
