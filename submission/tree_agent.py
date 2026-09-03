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


def settle(tree: ProofTree, node) -> bool:
    """A placeholder with no goal goes; several goals behind one placeholder
    become a scaffold node (case tags or bullets) with one leaf each. True
    when the tree changed and needs another look."""

    changed = False
    for sub in list(node.subgoals):
        if sub.tactic is not None:
            continue
        goals = split_goals(sub.text) if sub.text else []
        if not goals:
            node.subgoals.remove(sub)
            changed = True
        elif len(goals) > 1:
            tags = [m.group(1) for m in (re.match(r"case (\S+)", g) for g in goals) if m]
            if len(tags) == len(goals):
                scaffold = "\n".join(f"case {t} =>\n  sorry" for t in tags)
            else:
                scaffold = "\n".join("· sorry" for _ in goals)
            tree.expand(sub, scaffold, goals)
            sub.tactic.scaffold = True
            changed = True
    return changed


async def look(forest: Forest, lean, timeout_s: float | None = None):
    """One check of the rendering with every placeholder as `skip`; the
    printed goals flow to the leaves. Returns Lean's result."""

    from submission.board_agent import render_all
    check = await lean.check_file(render_all(forest.render()), timeout_s=timeout_s)
    observe(forest, check.messages, check.accepted)
    return check


async def attempt(forest: Forest, tree: ProofTree, leaf: GoalNode, block: str, lean,
                  timeout_s: float | None = None) -> tuple[bool, list]:
    """Try a block at a leaf: expand with one subgoal per `sorry` line plus one
    for whatever the block leaves open, look, settle. On a real failure the
    expansion is retracted and the messages come back as feedback."""

    from submission.framework import classify

    sorries = sum(1 for l in block.split("\n") if l.strip() == "sorry")
    tree.expand(leaf, block, [""] * (sorries + 1))
    for _ in range(4):
        check = await look(forest, lean, timeout_s)
        progress, spare, expensive, failures = classify(check.messages)
        if failures or expensive or check.timed_out:
            tree.retract(leaf)
            return False, list(check.messages)
        if not settle(tree, leaf.tactic):
            return True, list(check.messages)
    return True, list(check.messages)


# ---------------------------------------------------------------------------
# Slice 3: the smallest loop that proves something on the tree. One worker,
# no audit yet, closers as one `first` block; every undo is `drop`.

import time
from typing import Any

from re_harness import AgentResult, Problem, Services

from submission.agent import Ledger, declared_names, format_messages, in_file_coordinates, normalise_imports, strip_fences
from submission.board_agent import (BoardAgent, dialect, existential, read_witnesses,
                                    witness_search_file)
from submission.framework_agent import STEP_TOKENS, notes_for, screen_step, sheet_for

LEAF_TRIES = 4          # attempts at one leaf before its block is dropped
GOAL_DROPS = 2          # drops at one leaf before its parent goal is dropped
CLOSERS = "first\n  | omega\n  | norm_num\n  | simp\n  | decide\n  | trivial\n  | linarith\n  | positivity\n  | rfl"


class TreeAgent(BoardAgent):
    """The board agent's judge, prompts and probes on a proof tree."""

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        services = in_file_coordinates(services)
        cfg, started = self.config, time.monotonic()
        deadline = started + cfg.last_turn_start_s
        ledger, events = Ledger(), []
        text = normalise_imports(problem.challenge, problem.challenge)
        forest = forest_from_challenge(text)
        graded = declared_names(problem.challenge)
        lean = services.lean
        tree_of = {id(leaf): t for t in forest.trees for leaf in t.leaves()}
        drops: dict[int, int] = {}
        feedback: dict[int, str] = {}
        imports = "\n".join(l for l in text.split("\n") if l.startswith("import "))

        def tree_for(leaf: GoalNode) -> ProofTree:
            g = leaf
            while g.parent is not None:
                g = g.parent.goal
            return next(t for t in forest.trees if t.root is g)

        def result(how: str, accepted: bool) -> AgentResult:
            return AgentResult(forest.render(), {
                "strategy": "tree", "solved_by": how, "accepted_by_repl": accepted,
                "spend_usd": round(ledger.spent_usd, 6),
                "wall_s": round(time.monotonic() - started, 1),
                "turns": len(events), "events": events[-200:]})

        await look(forest, lean)   # the goals of the untouched file

        while time.monotonic() < deadline and ledger.spent_usd < 0.9 * cfg.budget_usd:
            leaves = forest.leaves()
            if not leaves:
                final = await lean.check_file(forest.render())
                events.append({"stage": "verify", "accepted": final.accepted})
                services.checkpoint(forest.render(), {"accepted": final.accepted})
                return result("tree", final.accepted)
            leaf = min(leaves, key=lambda g: (g.tries, drops.get(id(g), 0)))
            tree = tree_for(leaf)
            if not leaf.swept:
                leaf.swept = True
                ok, _ = await attempt(forest, tree, leaf, CLOSERS, lean)
                events.append({"kind": "closers", "accepted": ok})
                if ok:
                    continue
                parsed = existential(leaf.text)
                if parsed:
                    names, body = parsed
                    probe = await lean.check_file(witness_search_file(imports, names, body), timeout_s=60)
                    found = read_witnesses(probe.messages)
                    events.append({"kind": "witnesses", "found": found})
                    for row in found:
                        ok, _ = await attempt(forest, tree, leaf,
                                              f"exact ⟨{', '.join(row)}, by norm_num⟩", lean)
                        if ok:
                            break
                    if ok:
                        continue
            model = cfg.lines[len(events) % len(cfg.lines)]
            parts = [f"Problem: {problem.description}".strip(),
                     "File:\n" + forest.render()[-6000:],
                     "What Lean reports as open, with its hypotheses. The active goal is "
                     f"the `sorry` number {leaves.index(leaf) + 1} of {len(leaves)}:\n{leaf.text[:3000]}"]
            sheet = sheet_for(leaf.text)
            if sheet:
                parts.append("Names the loaded Mathlib has for this goal's vocabulary, "
                             f"as #check prints them:\n{sheet}")
            if feedback.get(id(leaf)):
                parts.append("Your last step here was rejected. Lean said:\n" + feedback[id(leaf)])
            if leaf.history:
                parts.append("Blocks already tried and dropped at this goal:\n"
                             + "\n---\n".join(h[:300] for h in leaf.history[-3:]))
            parts.append("Reply with one ```lean code block containing only tactic lines, "
                         "and nothing before or after it. No explanation.")
            reply, why = await self._call(model, "\n\n".join(parts), STEP_TOKENS, services, ledger)
            block = dialect(screen_step(strip_fences(reply), allow_sorry=True)).strip()
            if not block or why == "length":
                leaf.tries += 1
                events.append({"kind": "step", "by": model, "accepted": False, "why": why or "empty"})
                continue
            ok, msgs = await attempt(forest, tree, leaf, block, lean)
            events.append({"kind": "step", "by": model, "accepted": ok, "block": block[:200]})
            if ok:
                feedback.pop(id(leaf), None)
                continue
            leaf.tries += 1
            said = format_messages(msgs)[:1500]
            feedback[id(leaf)] = f"{said}\n{notes_for(said)}".strip()
            if leaf.tries >= LEAF_TRIES:
                # the leaf's own attempts are its history; if it keeps failing,
                # the step that produced it was the wrong one: drop one level up
                drops[id(leaf)] = drops.get(id(leaf), 0) + 1
                leaf.tries = 0
                above = leaf.parent_goal()
                if drops[id(leaf)] >= GOAL_DROPS and above is not None:
                    events.append({"kind": "drop", "at": "parent", "goal": above.text[-120:]})
                    tree.drop(above)
                    await look(forest, lean)
        events.append({"stage": "stop", "leaves": len(forest.leaves())})
        services.checkpoint(forest.render(), {"accepted": False})
        return result("best_effort", False)
