"""The board's vocabulary: a goal, a board, an edit, and what is remembered."""

from __future__ import annotations
import re
from dataclasses import dataclass, field
from typing import Any, Sequence
from submission.framework import (DECL_HEAD, classify, line_of, message_line,
                                  message_span, proof_span, root_names)
from submission.framework_agent import NARRATES, STEP_TOKENS
from submission.state import Feedback

# One definition. board_agent.py had two, and the second silently won.
OPENERS, CLOSERS = "([{⟨", ")]}⟩"



@dataclass(frozen=True)
class Goal:
    """One placeholder: where it is now, and what Lean says it is."""

    line: int
    indent: str
    decl: str
    text: str
    stmt: str = field(default="", compare=False)   # what extract_goal printed here
    cell: int = field(default=0, compare=False)    # the marked span it sits in

    @property
    def key(self) -> tuple[str, str]:
        return self.decl, self.text


@dataclass
class Board:
    """The file, every goal on it, and what the last check said."""

    text: str
    goals: list[Goal] = field(default_factory=list)
    messages: list[dict[str, Any]] = field(default_factory=list)
    accepted: bool = False
    bid: int = 0
    ms: int = 0

    @property
    def score(self) -> tuple[int, int]:
        """Fewer open goals first; the tie goes to the older branch. (Proved
        `have`s were tried as the first key: a filler `have : True` counts.)"""
        return len(self.goals), self.bid

    def find(self, key: tuple[str, str]) -> Goal | None:
        return next((g for g in self.goals if g.key == key), None)

    def index(self, goal: Goal) -> int:
        """Where a goal sits among the placeholders, by content first: a goal
        object from an earlier board keeps its old line number."""
        keys = [g.key for g in self.goals]
        if goal.key in keys:
            return keys.index(goal.key)
        return [g.line for g in self.goals].index(goal.line)


def is_root_goal(text: str, goal: Goal) -> bool:
    """The placeholder that is a proof's whole body: its cell is the proof."""

    span = proof_span(text, goal.decl) if goal.decl else None
    if not span:
        return False
    head = DECL_HEAD.match(text[span[0]:span[1]])
    if not head:
        return False
    first = line_of(text, span[0]) + head.group(1).count("\n") + 1
    return goal.line == first


def shift_message(message: dict[str, Any], delta: int) -> dict[str, Any]:
    out = dict(message)
    for key in ("pos", "endPos"):
        pos = out.get(key)
        if isinstance(pos, dict) and isinstance(pos.get("line"), int):
            out[key] = dict(pos, line=pos["line"] + delta)
    return out


def all_cell_spans(text: str):
    from submission.cells import all_spans
    return all_spans(text)


def owner(text: str, line: int) -> str:
    """The proof declaration a line is inside, if any."""

    for name in root_names(text):
        span = proof_span(text, name)
        if span and line_of(text, span[0]) <= line <= line_of(text, max(span[1] - 1, span[0])):
            return name
    return ""


HAVE_HEAD = re.compile(r"^(\s*)(have\b.*?)\s*:=\s*by\s*$")


DECL_NAME = re.compile(r"\s*(?:private\s+)?(?:theorem|lemma)\s+[\w'.]+")


HAVE_NAME = re.compile(r"^\s*have\s+([A-Za-z_][\w'.]*)\s*(?::|:=)")


def split_top(s: str, sep: str) -> tuple[str, str] | None:
    """`s` split at the first `sep` outside every bracket; None without one."""
    depth = 0
    for i, ch in enumerate(s):
        depth += (ch in OPENERS) - (ch in CLOSERS)
        if depth == 0 and s.startswith(sep, i) and not s.startswith(":=", i):
            return s[:i], s[i + len(sep):]
    return None


def narrates(model: str) -> bool:
    return any(n in model for n in NARRATES)


# Measured over 808 gpt-oss replies at 6000 tokens: p95 146–182 s and 2
# ReadTimeouts at the harness's 180 s, each closing the problem's ledger. At the
# slow rate seen 6000 tokens cannot finish inside 180 s; 4000 can. qwen: max 60 s.
SLOW_STEP_TOKENS = 4000


def step_tokens(model: str) -> int:
    return STEP_TOKENS if narrates(model) else SLOW_STEP_TOKENS


def binder_names(group: str) -> list[str]:
    parts = split_top(group[1:-1], ":")
    return parts[0].split() if parts else []


def signature(text: str, decl: str) -> str:
    """A declaration's statement with its name and whitespace taken out."""
    span = proof_span(text, decl)
    head = DECL_HEAD.match(text[span[0]:span[1]]) if span else None
    if not head:
        return decl
    stmt = DECL_NAME.sub("", head.group(1), count=1) if DECL_NAME.match(head.group(1)) else head.group(1)
    return " ".join(stmt.rsplit(":=", 1)[0].split())


INTRO_LIKE = re.compile(r"^\s*(intro|intros|rintro|obtain|rcases|cases'?|induction'?|by_contra'?|"
                        r"by_cases|interval_cases|fin_cases|match|choose|generalize|set)\b")


def hypotheses(goal_text: str) -> dict[str, str]:
    """Name -> printed type for each hypothesis line of a goal (first case only)."""
    head = goal_text.split("⊢", 1)[0] if "⊢" in goal_text else ""
    out: dict[str, str] = {}
    for line in head.split("\n"):
        if line[:1].isspace() or line.startswith("case ") or " : " not in line:
            continue
        names, typ = line.split(" : ", 1)
        for n in names.split():
            out[n] = typ.strip()
    return out


def groups(text: str) -> list[str]:
    """Every balanced parenthesised expression in a text, nesting included."""
    out, stack = [], []
    for i, ch in enumerate(text):
        if ch == "(":
            stack.append(i)
        elif ch == ")" and stack:
            out.append(text[stack.pop():i + 1])
    return [g for g in out if len(g) >= 8]


@dataclass
class GoalRecord:
    """What the ladder remembers about one goal.

    One record per goal in place of a container per thing remembered, so that
    `has this goal been through the leaf sweep` is a field and not a question
    about which of fifteen tables to look in."""

    tries: int = 0
    said: Feedback | None = None
    plan: str | None = None
    known_stmt: str = ""
    claimed_by: str | None = None
    recalled: bool = False
    swept: bool = False
    searched: bool = False
    divided: bool = False
    unsplittable: bool = False
    leaf_restarted: bool = False
    shelved: str = ""
    hint: str = ""
    # Measured on putnam_2020_a2: one model sent the same rejected step to the
    # same goal 274 times in 23 min. A goal a model repeats itself on goes to
    # the end of that model's line, so the other model sees it first.
    repeated: set[str] = field(default_factory=set)
    refused: set[str] = field(default_factory=set)

    def forget(self) -> None:
        """The attempt history a restart rolls back, and only that: what was
        tried, what Lean said, the plan. What the harness learned about the
        goal's shape survives, because the shape did not change."""
        self.tries, self.said, self.plan = 0, None, None

    def reject(self, author: str, why: str, kind: str = "rejected") -> None:
        """What the next model is told, and one more try against this goal.
        Four other places set `said` alone, to report without costing a try."""
        self.said = Feedback(author, why, kind)
        self.tries += 1


class Notes(dict):
    """Goal key to record, making one on first mention."""

    def __missing__(self, key: tuple[str, str]) -> GoalRecord:
        self[key] = GoalRecord()
        return self[key]

    def busy(self) -> bool:
        """Whether any worker is mid-step on any goal."""
        return any(r.claimed_by for r in self.values())

    def claim(self, key: tuple[str, str], model: str) -> None:
        if self[key].claimed_by is None:
            self[key].claimed_by = model

    def release(self, key: tuple[str, str], model: str) -> None:
        """Only what this model holds. `pick` offers a goal the other model
        has claimed, so an unguarded release drops a claim still in flight."""
        if self[key].claimed_by == model:
            self[key].claimed_by = None

    def forget(self, key: tuple[str, str]) -> None:
        self[key].forget()

    def forget_decl(self, decl: str) -> None:
        for key, record in self.items():
            if key[0] == decl:
                record.forget()

    def forget_repeats(self) -> None:
        for record in self.values():
            record.repeated.clear()


def author_free(record: GoalRecord, model: str) -> bool:
    """Whether this model has not already repeated itself on this goal."""
    return model not in record.repeated


def inherit(old: Sequence[Goal], new: Sequence[Goal], notes: Notes) -> None:
    """A goal whose key vanished because a fact was added above it keeps its
    history: the one new goal of the same declaration and target whose
    hypotheses contain the old ones takes over what was tried, what Lean said,
    and the plan. The rest is about the old key and stays there."""
    kept = {g.key for g in new}
    fresh = [g for g in new if g.key not in {o.key for o in old}]
    for g in old:
        if g.key in kept:
            continue
        hyps, target = set(hypotheses(g.text)), target_of(g.text)
        matches = [n for n in fresh if n.decl == g.decl and target_of(n.text) == target
                   and hyps <= set(hypotheses(n.text))]
        if len(matches) != 1:
            continue
        was, now = notes[g.key], notes[matches[0].key]
        if was.tries and not now.tries:
            now.tries = was.tries
        if was.said is not None and now.said is None:
            now.said = was.said
        if was.plan is not None and now.plan is None:
            now.plan = was.plan


def reparent_target(text: str, region: tuple[int, int], focus: Any,
                    goals: Sequence[Goal], errors: Sequence[Any]) -> Any:
    """The cell closed with no goal of its own, so Lean reports the parent's
    goal on the parent's header: the id to check next, or None."""

    if not isinstance(focus, int) or errors:
        return None
    if any(region[0] <= g.line <= region[1] for g in goals):
        return None
    above = [sp for sp in all_cell_spans(text) if sp.holds(region[0]) and sp.id != focus]
    parent = max(above, key=lambda sp: sp.start).id if above else owner(text, region[0])
    return parent if parent and parent != focus else None


def carry_goals(base_goals: Sequence[Goal], found: Sequence[Goal], probed: set[int],
                old: tuple[int, int], nested_old: set[Any]) -> list[Goal] | None:
    """A goal on a probed line was checked; every other goal keeps the text
    and statement it had on the base board, matched by file order. None when
    that count changed, which is the caller's signal to check the whole file."""

    outside_old = [g for g in base_goals
                   if not old[0] <= g.line <= old[1]
                   or (g.cell in nested_old and g.cell != 0)]
    if len(outside_old) != len([g for g in found if g.line not in probed]):
        return None
    goals, carried = [], iter(outside_old)
    for g in found:
        if g.line in probed:
            goals.append(g)
            continue
        was = next(carried)
        goals.append(Goal(g.line, g.indent, g.decl, was.text, was.stmt, g.cell))
    return goals


def carry_messages(base_messages: Sequence[Any], base_goals: Sequence[Goal],
                   goals: Sequence[Goal], probed: set[int], old: tuple[int, int],
                   delta: int, cut: int, nested_old: set[Any]) -> list[Any]:
    """The base's messages about everything this check did not look at, moved
    by however much the checked region grew."""

    holes = [g.line for g in goals if g.line not in probed]
    inner_old = {g.line for g in base_goals if old[0] <= g.line <= old[1]
                 and g.cell in nested_old and g.cell != 0}
    kept = []
    for m in base_messages:
        at = message_line(m)
        if at is None or (old[0] <= at <= old[1] and not (
                m in classify([m])[0] and any(
                    (message_span(m) or (at, at))[0] <= h <= (message_span(m) or (at, at))[1]
                    for h in inner_old))):
            continue
        m = shift_message(m, delta) if at > cut else m
        span = message_span(m)
        if m in classify([m])[0] and span and not any(span[0] <= h <= span[1] for h in holes):
            # A goal report from before the edit that no placeholder outside
            # the checked unit sits under is about the goal just closed.
            continue
        kept.append(m)
    return kept


def target_of(goal_text: str) -> str:
    return goal_text.rsplit("⊢", 1)[-1].strip() if "⊢" in goal_text else ""


def hyp_count(goal_text: str) -> int:
    """Hypothesis lines: those before `⊢` that carry a `:`, `case` lines aside."""

    head = goal_text.rsplit("⊢", 1)[0] if "⊢" in goal_text else goal_text
    return sum(1 for l in head.split("\n") if ":" in l and not l.startswith("case "))


@dataclass
class Edit:
    """What one reply asks for: a step at a goal, a proof of a named
    declaration, or a new lemma with its proof."""

    kind: str
    body: str
    name: str = ""
    block: str = ""

