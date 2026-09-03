"""A board of open goals, each known by its content, two models working two
of them at once; Lean judges every edit against the whole file. The file is
still the proof; a reply is read once, as a proof of whatever it names."""


from __future__ import annotations

import asyncio
import json
import re
import time
from dataclasses import dataclass, field
from typing import Any, Sequence

from re_harness import AgentResult, LLMCallError, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.lean import LeanRuntimeError

from submission.agent import (
    BUDGET_HEADROOM,
    FEEDBACK_CHARS,
    Config,
    Ledger,
    answer_names,
    declared_names,
    format_messages,
    grade,
    normalise_imports,
    scoring_faults,
    split_files,
    sweep_files,
    usable_cocktail,
)
from submission.framework import (
    DECLARATION,
    DECL_HEAD,
    as_goal,
    axiom_probe,
    classify,
    declaration_name,
    definition_slots,
    fill_definition,
    drop_lines,
    goal_text,
    graded_theorems,
    hand_to_search,
    in_span,
    insert_above,
    insert_preamble,
    is_done,
    line_of,
    message_line,
    message_text,
    message_span,
    normalise_steps,
    open_names,
    placeholders,
    prefixes,
    proof_body,
    proof_span,
    reindent,
    render,
    restate,
    root_names,
    split_cursor,
    sweep_body,
    unreachable,
)
from submission.framework_agent import (
    VACUOUS,
    BUDGET_RETRY,
    FILE_CHARS,
    NARRATES,
    ANSWER_TOKENS,
    strip_fences,
    GOAL_CHARS,
    LOOSE_DRAIN_S,
    MAX_PREFIXES,
    RAISED_BUDGETS,
    SLOW_COMPILE_MS,
    STEP_TOKENS,
    FRAMEWORK_SYSTEM,
    Feedback,
    FrameworkAgent,
    State,
    is_probe,
    notes_for,
    screen_step,
)

# The cursor loop's prompt, less "give every have a body": on the board a
# `have` may end in `sorry` and becomes a goal of its own.
BOARD_SYSTEM = FRAMEWORK_SYSTEM.replace(
    "  obtain, subst, left, right, exfalso, interval_cases, by_contra, show, rw.\n"
    "  A reshaping step goes alone, because it changes the goal for everything after.\n"
    "- it asserts a new fact: a `have`. Give every `have` a body. Independent `have`s\n"
    "  may be sent together; Lean names each one that fails.",
    "  obtain, subst, left, right, exfalso, interval_cases, by_contra, show, rw.\n"
    "  A reshaping step goes alone, because it changes the goal for everything after.\n"
    "- it asserts a new fact: a `have`. A `have` whose proof is short gets its body;\n"
    "  one whose proof is long ends in `:= by sorry` and becomes a goal on the board,\n"
    "  proved in its own turn. When the proof left is more than about twenty lines,\n"
    "  post its facts this way and prove one of them, do not write it all at once:\n"
    "  a reply that runs past the token limit keeps only its complete steps.")
assert "goal on the board" in BOARD_SYSTEM

# Two rejections on a goal buy it a plan from the other model, as before.
PLAN_AFTER = 2
# A goal this many rejections deep is still open, only last in line. Time and
# money are the exits; a goal is never declared hopeless by count alone.
LAST_IN_LINE = 6
# A goal inside a `have ... := by` that has been rejected this many times takes
# the `have` down with it, and everything after it in its block: the board goes
# back to before the decomposition. Measured on rmo_2000_2: a false `have`
# posted at t=64 made every later goal a contradiction and the lemma unprovable.
WITHDRAW_AFTER = 4
# When every goal is last in line, the declaration holding the worst of them
# goes back to its statement, this many times at most.
MAX_RESTATES = 2
# A worker with no goal to take waits this long for the board to change.
IDLE_WAIT_S = 2.0
# What the model is told when its step ran the whole check into the timeout.
TIMED_OUT = ("that step timed out: the file no longer checks in time. The tactic "
             "is far too expensive (decide, omega or nlinarith over a large range, "
             "simp with a wide lemma set); the step was removed. Use interval_cases "
             "on a bounded variable, or state the cases as a disjunction and prove "
             "each with norm_num")
# A check is cut at a few times what the current file costs, never the harness's
# 120s: the slow-step guard refuses anything adding SLOW_STEP_MS anyway, and a
# timeout also forces a container restart (measured putnam_2018_a1: 36..82s each).
CHECK_TIMEOUT_FLOOR_S = 30
CHECK_TIMEOUT_CAP_S = 120


def check_timeout_s(base_ms: int) -> int:
    return min(CHECK_TIMEOUT_CAP_S, max(CHECK_TIMEOUT_FLOOR_S, (3 * base_ms + 20_000) // 1000))


# A step that makes the file slower to check by this much is refused as too
# expensive even when Lean raises no budget error: every later check pays it,
# and the comparator allows 180s. Measured on p09: one accepted step took the
# check from 1s to 38s, and the run then lost 5 minutes to a 120s timeout and
# the container restart that follows it.
SLOW_STEP_MS = 10_000
# There is no refutation probe. Proving `¬ target` from the context by
# decide/omega only refutes the goal when the context is consistent, and a
# proof by contradiction lives in an inconsistent one: on p09 the probe
# "refuted" six true goals (`h1 : n % 3 = 1 ... ⊢ False`) and undid the proof.
# Live branches: alternative proof files racing on the same problem. A second
# accepted answer to a goal one model already moved becomes a sibling branch
# rather than a stale reply. Measured on p09: the run was decided by one such
# choice at t=50s, and there was no way to hedge it.
BEAM = 2


@dataclass(frozen=True)
class Goal:
    """One placeholder: where it is now, and what Lean says it is."""

    line: int
    indent: str
    decl: str
    text: str

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
        """Fewer open goals first; the tie goes to the less-tried branch."""
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


def render_all(text: str) -> str:
    """Every placeholder as `skip`, so one check prints every goal."""

    out, shift = text, 0
    for match in placeholders(text):
        start, end = match.start() + shift, match.end() + shift
        out = out[:start] + f"{match.group(1)}skip" + out[end:]
        shift += len("skip") - (match.end() - match.start() - len(match.group(1)))
    return out


def owner(text: str, line: int) -> str:
    """The proof declaration a line is inside, if any."""

    for name in root_names(text):
        span = proof_span(text, name)
        if span and line_of(text, span[0]) <= line <= line_of(text, max(span[1] - 1, span[0])):
            return name
    return ""


def read_board(text: str, messages: Sequence[dict[str, Any]], accepted: bool) -> Board:
    """Each placeholder takes the tightest `unsolved goals` span holding it."""

    spans = [(m, message_span(m)) for m in classify(messages)[0]]
    goals = []
    for match in placeholders(text):
        line = line_of(text, match.start())
        fits = [(s[1] - s[0], goal_text(m)) for m, s in spans if s and s[0] <= line <= s[1]]
        goals.append(Goal(line, match.group(1), owner(text, line),
                          min(fits, key=lambda f: f[0])[1] if fits else ""))
    return Board(text, goals, list(messages), accepted)


META = re.compile(r"\?[\w.]+|^(?:Type|Sort)\b")


HAVE_HEAD = re.compile(r"^(\s*)(have\b.*?)\s*:=\s*by\s*$")
# A goal whose statement the model wrote, as opposed to one Lean derived from an
# `intro` or `rcases`. Measured: auditing every new goal was 48% of the wall
# clock under the lock, and every false statement caught was a `have`.
STATED_HEAD = re.compile(r"^(\s*)((?:have|suffices|show|obtain)\b.*?)\s*:=\s*by\s*$")


CLOSER_TAG = re.compile(r"^closer (\d+)$")
DECL_NAME = re.compile(r"\s*(?:private\s+)?(?:theorem|lemma)\s+[\w'.]+")
HAVE_NAME = re.compile(r"^\s*have\s+([A-Za-z_][\w'.]*)\s*(?::|:=)")


# Tactics that evaluate a closed statement; none of them uses a hypothesis
# from the context, so every hypothesis is proved at the values, not assumed.
WITNESS_CLOSERS = ("norm_num", "decide", "simp",
                   "norm_num [Finset.mem_insert, Finset.mem_singleton]",
                   "simp; norm_num", "norm_num; decide")
AUDIT_TOKENS = 2500
AUDIT_SYSTEM = ("You audit one goal inside a Lean 4 proof. You answer with one "
                "JSON object and nothing else.")
# Lean states the goal itself: every hypothesis in scope as a binder, numerals
# typed so the text elaborates again on its own.
EXTRACT = "set_option pp.numericTypes true in extract_goal"
EXTRACTED = re.compile(r"theorem\s+[\w'.]*extracted_\d+\s*(.*)", re.S)
OPENERS, CLOSERS = "({[⦃", ")}]⦄"
# Measured on the graded image: Lean's severity string is `info`.
INFO = ("info", "information")


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


def extract_file(text: str, goals: Sequence[Goal]) -> str:
    """The file with these goals' placeholders asking Lean to state them."""
    lines = render_all(text).split("\n")
    for g in goals:
        lines[g.line - 1] = g.indent + EXTRACT
    return "\n".join(lines)


def have_extract_file(lines: Sequence[str], at: Sequence[int]) -> tuple[str, dict[int, int]]:
    """The file with these `have`s' bodies replaced by a request to state the
    claim; the map from each have's line index to the line Lean answers on."""
    out, where, shift, i = [], {}, 0, 0
    marks = set(at)
    text_lines = render_all("\n".join(lines)).split("\n")
    while i < len(text_lines):
        ln = text_lines[i]
        out.append(ln)
        head = HAVE_HEAD.match(ln) if i in marks else None
        if not head:
            i += 1
            continue
        depth = len(head.group(1))
        j = i + 1
        while j < len(text_lines) and (not text_lines[j].strip()
                                       or len(text_lines[j]) - len(text_lines[j].lstrip()) > depth):
            j += 1
        out.append(" " * (depth + 2) + EXTRACT)
        where[i] = len(out)
        i = j
    return "\n".join(out), where


def statements(messages: Sequence[Any]) -> dict[int, str]:
    """Line -> the statement `extract_goal` printed there, binders and target."""
    out: dict[int, str] = {}
    for m in messages:
        if not isinstance(m, dict) or m.get("severity") not in INFO:
            continue
        found, line = EXTRACTED.search(message_text(m)), message_line(m)
        if found and line is not None:
            body = found.group(1)
            out[line] = " ".join(body.rsplit(":=", 1)[0].split())
    return out


def split_statement(stmt: str) -> tuple[list[str], str] | None:
    """Binder groups and target of a stated goal; None if it reads unusually."""
    groups, depth, buf = [], 0, ""
    for i, ch in enumerate(stmt):
        if depth == 0 and ch == ":":
            return groups, stmt[i + 1:].strip()
        if depth == 0 and not ch.isspace() and ch not in OPENERS:
            return None
        depth += (ch in OPENERS) - (ch in CLOSERS)
        buf += ch
        if depth == 0 and ch in CLOSERS:
            groups.append(buf.strip())
            buf = ""
    return None


def claim_of(have_statement: str) -> str:
    """The proposition in `have h : P`; "" when there is no top-level colon."""
    parts = split_top(have_statement, ":")
    return parts[1].strip() if parts and parts[0].startswith("have") else ""


def binder_names(group: str) -> list[str]:
    parts = split_top(group[1:-1], ":")
    return parts[0].split() if parts else []


def witness_file(prefix: str, groups: Sequence[str], values: dict[str, str],
                 target: str) -> str:
    """One `example`: the binders the auditor assigned stay binders, pinned to
    the values; every other binder is a hypothesis to prove there, and the
    target must fail. Only evaluation closes it, so a pass is a refutation."""
    keep, hyps = [], []
    for g in groups:
        names = binder_names(g)
        if names and all(n in values for n in names):
            keep.append("(" + g[1:-1] + ")")
        else:
            parts = split_top(g[1:-1], ":")
            hyps.append((parts[1] if parts else g[1:-1]).strip())
    fixed = " ".join(f"(w_{n} : {n} = ({v}))" for n, v in values.items())
    body = " ∧ ".join([f"({h})" for h in hyps] + [f"¬ ({target})"])
    binders = " ".join([*keep, fixed]).strip()
    return (prefix.rstrip() + f"\n\nexample {binders} : {body} := by\n  subst_vars\n  first\n"
            + "".join(f"  | ({t}; done)\n" for t in WITNESS_CLOSERS))


def audit_prompt(stmt: str, definitions: str) -> str:
    parts = ["A goal inside a Lean 4 proof, exactly as Lean states it: every "
             f"hypothesis in scope is a binder, the target follows the last colon.\n{stmt}"]
    if definitions.strip():
        parts.append(f"Definitions in scope:\n{definitions.strip()[:1500]}")
    parts.append(
        "Is the target a consequence of the hypotheses? If not, give one "
        "counterexample: a Lean term for every variable binder (leave the "
        'hypothesis binders out), as {"counterexample": {"x": "..."}}. Use small '
        "concrete values and check every hypothesis by hand before answering. "
        'If the target does follow, answer {"holds": true}.')
    return "\n\n".join(parts)


def read_witness(reply: str) -> dict[str, str] | None:
    """The values a reply names, or None (holds / unreadable)."""
    found = re.search(r"\{.*\}", reply, re.S)
    try:
        given = json.loads(found.group(0)).get("counterexample") if found else None
    except (ValueError, AttributeError):
        return None
    if not isinstance(given, dict) or not given:
        return None
    return {str(n): str(v).strip() for n, v in given.items()}


def tagged_closers(cocktail: Sequence[str]) -> str:
    """The cocktail as one `first`, each alternative announcing itself, so the
    check that closes the goal also says which closer did it."""
    return "first\n" + "\n".join(f'| (trace "closer {i}"; {t}; done)'
                                  for i, t in enumerate(cocktail))


def fired_closer(messages: Sequence[Any], span: tuple[int, int],
                 cocktail: Sequence[str]) -> str | None:
    """The alternative that closed the goal: the last tag reported inside the
    block, whether or not Lean kept the tags of the alternatives that failed."""
    hits = []
    for m in messages:
        if not isinstance(m, dict) or m.get("severity") not in INFO:
            continue
        tag = CLOSER_TAG.match(str(m.get("data", "")).strip())
        line = message_line(m)
        if tag and line is not None and span[0] <= line <= span[1]:
            hits.append((line, int(tag.group(1))))
    return cocktail[max(hits)[1]] if hits else None


def enclosing_have(lines: Sequence[str], goal: Goal) -> tuple[int | None, re.Match | None]:
    """The nearest shallower line above the goal, and its `have ... := by` head."""
    i = goal.line - 1
    above = next((j for j in range(i - 1, -1, -1) if lines[j].strip()
                  and len(lines[j]) - len(lines[j].lstrip()) < len(goal.indent)), None)
    return above, (HAVE_HEAD.match(lines[above]) if above is not None else None)


SET_LITERAL = re.compile(r"^\(?\s*\{(.*)\}\s*(?::.*?)?\)?\s*$", re.S)
TUPLE_IN = re.compile(r"[⟨(]\s*([A-Za-z_][\w']*(?:\s*,\s*[A-Za-z_][\w']*)+)\s*[⟩)]\s*∈")


def set_elements(term: str) -> list[list[str]] | None:
    """The tuples of an explicit finite set literal, or None for any other term."""
    found = SET_LITERAL.match(term.strip())
    if not found or "|" in found.group(1):
        return None
    items, depth, buf = [], 0, ""
    for ch in found.group(1):
        if ch == "," and depth == 0:
            items.append(buf.strip()); buf = ""
            continue
        depth += (ch in OPENERS) - (ch in CLOSERS)
        buf += ch
    if buf.strip():
        items.append(buf.strip())
    out = []
    for it in items:
        inner = it.strip()
        if inner[:1] in "(⟨" and inner[-1:] in ")⟩":
            inner = inner[1:-1]
        parts, depth, buf = [], 0, ""
        for ch in inner:
            if ch == "," and depth == 0:
                parts.append(buf.strip()); buf = ""
                continue
            depth += (ch in OPENERS) - (ch in CLOSERS)
            buf += ch
        parts.append(buf.strip())
        out.append(parts)
    return out


def signature(text: str, decl: str) -> str:
    """A declaration's statement with its name and whitespace taken out."""
    span = proof_span(text, decl)
    head = DECL_HEAD.match(text[span[0]:span[1]]) if span else None
    if not head:
        return decl
    stmt = DECL_NAME.sub("", head.group(1), count=1) if DECL_NAME.match(head.group(1)) else head.group(1)
    return " ".join(stmt.rsplit(":=", 1)[0].split())


def drop_declaration(text: str, decl: str) -> str:
    """The file without one declaration (its head, its proof, its doc comment)."""
    span = proof_span(text, decl)
    if not span:
        return text
    start = text.rfind("\n\n", 0, span[0])
    start = 0 if start < 0 else start + 2
    return text[:start] + text[span[1]:]


def is_stated(lines: Sequence[str], goal: Goal) -> bool:
    """Whether the goal is the body of a statement the model wrote."""
    i = goal.line - 1
    above = next((j for j in range(i - 1, -1, -1) if lines[j].strip()
                  and len(lines[j]) - len(lines[j].lstrip()) < len(goal.indent)), None)
    if above is None:
        return False
    if STATED_HEAD.match(lines[above]):
        return True
    # A declaration's own root goal (the placeholder right under its head) is a
    # statement the model wrote when the declaration was hoisted; a goal deeper
    # in a graded theorem's body is not.
    return DECLARATION.match(lines[above]) is not None and above == i - 1


def enclosing_chain(lines: Sequence[str], goal: Goal) -> list[tuple[int, re.Match]]:
    """Every `have ... := by` the goal sits inside, nearest first."""
    chain, probe = [], goal
    while True:
        above, head = enclosing_have(lines, probe)
        if not head:
            return chain
        chain.append((above, head))
        probe = Goal(above + 1, head.group(1), goal.decl, goal.text)


def split_facts(block: str) -> tuple[list[str], str]:
    """The `have ... := by sorry` statements at the top level of a block, and
    the block without them."""
    lines = normalise_steps(block).split("\n")
    body = [l for l in lines if l.strip()]
    base = min((len(l) - len(l.lstrip()) for l in body), default=0)
    facts, rest, i = [], [], 0
    while i < len(lines):
        line = lines[i]
        head = HAVE_HEAD.match(line)
        nxt = lines[i + 1] if i + 1 < len(lines) else ""
        if head and len(head.group(1)) == base and nxt.strip() == "sorry" \
                and len(nxt) - len(nxt.lstrip()) > base:
            facts.append(f"{line.strip()}\n  sorry")
            i += 2
            continue
        rest.append(line)
        i += 1
    return facts, "\n".join(rest).strip("\n")


def restates(block: str, claims: Sequence[str]) -> bool:
    """Whether a block posts a `have` whose claim is one of these."""
    gone = {" ".join(c.split()) for c in claims}
    for line in block.split("\n"):
        head = HAVE_HEAD.match(line) or re.match(r"^(\s*)(have\b.*?)\s*:=", line)
        if head and " ".join(claim_of(head.group(2).strip()).split()) in gone:
            return True
    return False


def proved_facts(text: str, goal: Goal) -> dict[str, str]:
    """Claim -> name for every proved `have` (no placeholder in its block) that
    is in scope at the goal: above it, and its block not yet closed."""
    lines = text.split("\n")
    out: dict[str, str] = {}
    for i in range(goal.line - 1):
        head = HAVE_HEAD.match(lines[i])
        name = HAVE_NAME.match(lines[i]) if head else None
        if not (head and name) or len(head.group(1)) > len(goal.indent):
            continue
        depth = len(head.group(1))
        j = i + 1
        while j < len(lines) and (not lines[j].strip()
                                  or len(lines[j]) - len(lines[j].lstrip()) > depth):
            j += 1
        between = [l for l in lines[j:goal.line - 1] if l.strip()]
        if any(len(l) - len(l.lstrip()) < depth for l in between):
            continue
        if not any(l.strip() == "sorry" for l in lines[i + 1:j]):
            out[" ".join(claim_of(head.group(2).strip()).split())] = name.group(1)
    return out


def stated_facts(text: str, decl: str) -> dict[str, str]:
    """Claim -> name for every `have` already inside a declaration's proof."""
    span = proof_span(text, decl)
    out: dict[str, str] = {}
    for line in (text[span[0]:span[1]] if span else "").split("\n"):
        head = HAVE_HEAD.match(line)
        name = HAVE_NAME.match(line) if head else None
        if head and name:
            out[" ".join(claim_of(head.group(2).strip()).split())] = name.group(1)
    return out


def withdraw(text: str, goal: Goal) -> tuple[str, str]:
    """The file with the `have` enclosing this goal, and the rest of its block,
    cut back to one `sorry`; the withdrawn statement second. ("", "") when the
    nearest shallower line above the goal is not a `have ... := by`."""
    lines = text.split("\n")
    i = goal.line - 1
    above, head = enclosing_have(lines, goal)
    if not head:
        return "", ""
    indent = head.group(1)
    end = i + 1
    while end < len(lines) and (not lines[end].strip()
                                or len(lines[end]) - len(lines[end].lstrip()) >= len(indent)):
        end += 1
    while end - 1 > i and not lines[end - 1].strip():
        end -= 1
    return "\n".join(lines[:above] + [indent + "sorry"] + lines[end:]), head.group(2).strip()


INFLATION = 3.0


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


def inflated(before: str, after: str) -> float:
    """How much larger the hypotheses both goals share became, when the growth
    is one new bracketed expression repeated 3 times or more: a rewrite that
    unfolds a variable everywhere. Unfolding a set literal is not repetition."""
    old, new = hypotheses(before), hypotheses(after)
    shared = [n for n in old if n in new]
    was = sum(len(old[n]) for n in shared)
    now_text = "\n".join(new[n] for n in shared)
    old_text = "\n".join(old[n] for n in shared)
    if was < 40:
        return 1.0
    fresh = [g for g in set(groups(now_text)) if g not in old_text]
    if not any(now_text.count(g) >= 3 for g in fresh):
        return 1.0
    return len(now_text) / was


def target_of(goal_text: str) -> str:
    return goal_text.rsplit("⊢", 1)[-1].strip() if "⊢" in goal_text else ""


def hyp_count(goal_text: str) -> int:
    """Hypothesis lines: those before `⊢` that carry a `:`, `case` lines aside."""

    head = goal_text.rsplit("⊢", 1)[0] if "⊢" in goal_text else goal_text
    return sum(1 for l in head.split("\n") if ":" in l and not l.startswith("case "))


def salvage(reply: str) -> str:
    """A reply cut mid-statement, less the statement it was cut in. Measured on
    rmo_2001_2: 37 of 70 step replies from one model ended at the token cap."""

    text = reply + ("\n```" if reply.count("```") % 2 else "")
    cuts = prefixes(screen_step(text, allow_sorry=True))
    return cuts[0] if cuts else ""


HAVE_OPEN = re.compile(r"^(\s*)(have|suffices|show|obtain)\b")


def fold_heads(block: str) -> str:
    """A statement split over several lines, joined onto its first line, so
    that every reader of the board (audit, lift, withdraw, restate) sees it.
    Lean does not mind the line length."""
    lines, out, i = block.split("\n"), [], 0
    while i < len(lines):
        line = lines[i]
        head = HAVE_OPEN.match(line)
        if head and ":=" not in line:
            depth, j, joined = len(head.group(1)), i + 1, line.rstrip()
            while j < len(lines) and lines[j].strip() and \
                    len(lines[j]) - len(lines[j].lstrip()) > depth:
                joined += " " + lines[j].strip()
                if ":=" in lines[j]:
                    j += 1
                    break
                j += 1
            if ":=" in joined:
                out.append(joined)
                i = j
                continue
        out.append(line)
        i += 1
    return "\n".join(out)


BIG_OPERATOR_IN = re.compile(r"([∑∏]\s*(?:\([^()]*\)|[^\s,()]+))\s+in\s+")


def dialect(block: str) -> str:
    """Spellings the models learned that this Mathlib renamed, written the way
    it reads them now: `∑ x in s` is `∑ x ∈ s`. Lexical only, same term."""
    return BIG_OPERATOR_IN.sub(r"\1 ∈ ", block)


def put(text: str, goal: Goal, block: str, trailing: bool = True) -> tuple[str, tuple[int, int]]:
    """The block where the goal's placeholder is, and the lines it now covers."""

    lines = text.split("\n")
    body = reindent(normalise_steps(fold_heads(dialect(block))), goal.indent)
    if trailing:
        body = f"{body}\n{goal.indent}sorry"
    lines[goal.line - 1] = body
    return "\n".join(lines), (goal.line, goal.line + body.count("\n"))


def view(source: str, decl: str) -> tuple[str, int]:
    """The file as the model should read it: every statement in full, and only
    the body of the declaration being worked on. The `skip` line is recomputed.
    Measured on p09: the last 8000 chars of the file cut the shared lemma's
    statement off the top, and the model cited a lemma it could not see."""

    out, kept_lines = [], 0
    for name in root_names(source):
        span = proof_span(source, name)
        if not span or name == decl:
            continue
        body = source[span[0]:span[1]]
        head = DECL_HEAD.match(body)
        if not head or "skip" in body or "sorry" in body:
            continue
        lines = len([l for l in body[head.end():].split("\n") if l.strip()])
        out.append((span, f"{head.group(1)}\n  -- proved, {lines} lines elided\n\n"))
    for (start, end), replacement in sorted(out, reverse=True):
        source = source[:start] + replacement + source[end:]
    at = next((i for i, l in enumerate(source.split("\n"), start=1) if l.strip() == "skip"), 0)
    return source, at


@dataclass
class Edit:
    """What one reply asks for: a step at a goal, a proof of a named
    declaration, or a new lemma with its proof."""

    kind: str
    body: str
    name: str = ""
    block: str = ""


def interpret(reply: str, board: Board, goal: Goal, graded: Sequence[str]) -> list[Edit]:
    """Read a reply once, as proofs of whatever it names."""

    block = screen_step(reply, allow_sorry=True)
    if not block:
        return []
    if is_probe(block):
        return [Edit("probe", block)]
    lines, edits, plain, current = block.split("\n"), [], [], None
    for line in lines + [None]:
        head = DECLARATION.match(line) if line is not None else None
        if line is not None and not head:
            (current[1] if current else plain).append(line)
            continue
        if current:
            name, body = current[0], "\n".join(current[1])
            raw = "\n".join([current[2]] + current[1])
            if name in open_names(board.text):
                edits.append(Edit("prove", proof_body(raw, name), name))
            elif name in root_names(board.text) or name in graded:
                edits.append(Edit("drop", "", name))
            else:
                edits.append(Edit("hoist", proof_body(raw, name), name, as_goal(raw) or raw))
        current = [head.group(1), [], line] if head else None
    plain_body = "\n".join(plain).strip()
    if plain_body:
        edits.insert(0, Edit("step", plain_body))
    return edits


class BoardAgent(FrameworkAgent):
    """The cursor loop's primitives, driven by a board instead of a cursor."""

    async def _define(self, problem: Problem, text: str, services: Services,
                      ledger: Ledger, events: list[dict[str, Any]]) -> str:
        """The answer term is the first claim of the proof and the one no later
        step can repair, so every model offers one and each offer is audited
        against the theorem's own statement; a broken offer is not used."""

        for name, kind in definition_slots(text):
            offers: list[tuple[str, str]] = []
            note = ""
            for attempt in range(2 * len(self.config.lines)):
                model = self.config.lines[attempt % len(self.config.lines)]
                ask = (f"Give the value of `{name} : {kind}`.\n\nProblem: "
                       f"{problem.description}\n\nFile:\n{text[:FILE_CHARS]}\n\n"
                       f"Reply with one Lean 4 term of type `{kind}` on a single line, "
                       "and nothing else. It is the answer itself, not a proof of it, "
                       "so no tactics and no `by`. A finite set is written as its "
                       "elements, `({(1, 2), (3, 4)} : T)`, never as a set-builder." + note)
                # Measured one23b: with reasoning on, qwen answered the term
                # question with a page of derivation twice; gpt-oss alone offered.
                said, _ = await self._call(model, ask, ANSWER_TOKENS, services, ledger,
                                           think=not narrates(model))
                term = dialect(" ".join(strip_fences(said).split("\n")))[:FEEDBACK_CHARS].strip()
                if not term or term.startswith("by "):
                    note = "\n\nYour last reply was not a term."
                    continue
                candidate = fill_definition(text, name, term)
                check = await services.lean.check_file(candidate)
                if classify(check.messages)[3]:
                    note = ("\n\nThat term did not elaborate. Lean said:\n"
                            + format_messages(check.messages)[:FEEDBACK_CHARS])
                    continue
                note = ""
                if term not in [t for t, _ in offers]:
                    offers.append((term, candidate))
                if len(offers) >= 2 or attempt >= len(self.config.lines) and offers:
                    break
            chosen = None
            for term, candidate in offers:
                # The theorem that states the answer's role is the one audited.
                users = [n for n in root_names(candidate)
                         if (span := proof_span(candidate, n)) and name in candidate[span[0]:span[1]]]
                verdict, values = await self._audit_root(
                    candidate, (users or root_names(candidate))[0], services, ledger, term)
                events.append({"stage": "define", "name": name, "kept": verdict != "refuted",
                               "term": term[:120], "verdict": verdict, "values": values})
                if verdict != "refuted" and chosen is None:
                    chosen = candidate
            if chosen is None and offers:
                chosen = offers[0][1]
            if chosen is not None:
                text = chosen
        return text

    async def _share(self, problem: Problem, text: str, services: Services,
                     ledger: Ledger, events: list[dict[str, Any]]) -> str:
        """As the framework's, and each kept statement is audited: a shared
        lemma that a witness breaks does not enter the file."""

        before = set(root_names(text))
        text = await super()._share(problem, text, services, ledger, events)
        seen: set[str] = {signature(text, n) for n in before}
        for name in [n for n in root_names(text) if n not in before]:
            sig = signature(text, name)
            if sig in seen:
                # Measured on p09: both models proposed the same lemma under two
                # names and both were being proved.
                events.append({"stage": "share-audit", "name": name, "verdict": "duplicate"})
                text = drop_declaration(text, name)
                continue
            seen.add(sig)
            verdict, values = await self._audit_root(text, name, services, ledger)
            events.append({"stage": "share-audit", "name": name, "verdict": verdict,
                           "values": values})
            if verdict == "refuted":
                text = drop_declaration(text, name)
        return text

    async def _audit_root(self, text: str, decl: str, services: Services,
                          ledger: Ledger, term: str = "") -> tuple[str, dict[str, str]]:
        """A declaration's statement tried against a witness: Lean states its
        goal, each element of an explicit set answer (if `term` is one) and
        then the auditor's values are tried as values that make it fail."""

        roots = root_names(text)
        holes = [(line_of(text, m.start()), m.group(1)) for m in placeholders(text)]
        at = next(((l, ind) for l, ind in holes if owner(text, l) == decl), None)
        if not roots or at is None:
            return "unstated", {}
        goal = Goal(at[0], at[1], decl, "")
        check = await services.lean.check_file(extract_file(text, [goal]),
                                               timeout_s=CHECK_TIMEOUT_FLOOR_S)
        stmt = statements(check.messages).get(goal.line, "")
        parsed = split_statement(stmt) if stmt else None
        if not parsed:
            return "unstated", {}
        groups, target = parsed
        first = proof_span(text, roots[0])
        prefix = text[:first[0]] if first else ""
        names = [n for g in groups for n in binder_names(g)]
        tries: list[dict[str, str]] = []
        tuple_names = TUPLE_IN.search(target)
        elements = set_elements(term)
        if tuple_names and elements:
            keys = [k.strip() for k in tuple_names.group(1).split(",")]
            tries += [dict(zip(keys, e)) for e in elements if len(e) == len(keys)]
        async def breaks(values: dict[str, str]) -> bool:
            probe = await services.lean.check_file(witness_file(prefix, groups, values, target),
                                                   timeout_s=CHECK_TIMEOUT_FLOOR_S)
            return probe.accepted
        for values in tries:
            if await breaks(values):
                return "refuted", values
        auditor = next((m for m in self.config.lines if not narrates(m)), self.config.lines[0])
        reply, _ = await self._call(auditor, audit_prompt(stmt, prefix.replace("import Mathlib", "")),
                                    AUDIT_TOKENS, services, ledger, system=AUDIT_SYSTEM)
        given = {n: v for n, v in (read_witness(reply) or {}).items() if n in names}
        if (given or not names) and await breaks(given):
            return "refuted", given
        return ("holds" if tries or given or "holds" in reply else "unverified"), {}

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        cfg = self.config
        started = time.monotonic()
        deadline = started + cfg.last_turn_start_s
        ledger = Ledger()
        names = answer_names(problem.challenge)
        graded = declared_names(problem.challenge)
        text = normalise_imports(problem.challenge, problem.challenge)
        first_graded = next(iter(root_names(text)), "")
        best = text
        events: list[dict[str, Any]] = []
        models = list(cfg.lines)
        loose: list[asyncio.Task[Any]] = []
        lock = asyncio.Lock()
        changed = asyncio.Event()
        claimed: dict[tuple[str, str], str] = {}
        # Measured on putnam_2020_a2: one model sent the same rejected step to the
        # same goal 274 times in 23 min. A goal a model repeats itself on goes to
        # the end of that model's line, so the other model sees it first.
        repeated: set[tuple[tuple[str, str], str]] = set()
        tries: dict[tuple[str, str], int] = {}
        said: dict[tuple[str, str], Feedback] = {}
        plans: dict[tuple[str, str], str] = {}
        swept: set[tuple[str, str]] = set()
        divided: set[tuple[str, str]] = set()
        restated: dict[str, int] = {}
        refused: set[tuple[tuple[str, str], str]] = set()
        withdrawn: dict[str, list[str]] = {}
        audited: dict[tuple[str, str], str] = {}
        raised = False
        finished = False

        def time_left() -> float:
            return deadline - time.monotonic()

        def can_ask() -> bool:
            return ledger.spent_usd < BUDGET_HEADROOM * cfg.budget_usd

        def offer(candidate: str, accepted: bool) -> None:
            nonlocal best
            if accepted or not scoring_faults(candidate, names, problem.challenge):
                best = candidate
                services.checkpoint(best, {"accepted": accepted})

        def result(source: str, how: str, accepted: bool) -> AgentResult:
            tail = events[-60:]
            kept = [e for e in events[:-60] if "stage" in e] + tail
            return AgentResult(source, {
                "strategy": "board",
                "solved_by": how,
                "accepted_by_repl": accepted,
                "spend_usd": round(ledger.spent_usd, 6),
                "wall_s": round(time.monotonic() - started, 1),
                "turns": len(events),
                "events": kept,
            })

        async def deliver(text: str, how: str) -> AgentResult | None:
            state = await self._finish(State(text=text, accepted=True), services, time_left)
            check = await services.lean.check_file(
                axiom_probe(state.text, declared_names(problem.challenge)))
            faults, _ = grade(state.text, check, names, problem.challenge)
            events.append({"stage": "verify", "accepted": check.accepted,
                           "faults": faults[:5], "compile_ms": check.duration_ms,
                           "slow": check.duration_ms > SLOW_COMPILE_MS})
            if not check.accepted or faults:
                return None
            offer(state.text, True)
            return result(state.text, how, True)

        board = Board(text)
        branches: list[Board] = []
        sound: dict[int, str] = {}
        next_bid = 1

        def focus(b: Board) -> None:
            nonlocal board
            board = b

        def live(bid: int) -> Board | None:
            return next((b for b in branches if b.bid == bid), None)

        def prune() -> None:
            while len(branches) > BEAM:
                worst = max(branches, key=lambda b: (len(b.goals), -b.bid))
                branches.remove(worst)
                events.append({"stage": "prune", "bid": worst.bid, "goals": len(worst.goals)})

        async def look(candidate: str, base: Board | None = None) -> Board:
            check = await services.lean.check_file(
                render_all(candidate), timeout_s=check_timeout_s((base or board).ms))
            found = read_board(candidate, check.messages, check.accepted)
            found.ms = check.duration_ms
            return found

        async def commit(candidate: Board) -> None:
            """Make a board current, after its own housekeeping."""

            nonlocal board
            bid = board.bid
            fresh = await settle(candidate)
            fresh.bid = bid
            _, _, dear, broken = classify(fresh.messages)
            if broken or dear:
                if fresh.text != sound.get(bid, ""):
                    events.append({"stage": "repair", "bid": bid,
                                   "why": "cost" if dear and not broken else "error",
                                   "said": format_messages(broken or dear)[:300]})
                    fresh = await look(sound.get(bid, text))
                    fresh.bid = bid
            else:
                sound[bid] = fresh.text
            board = fresh
            for i, b in enumerate(branches):
                if b.bid == bid:
                    branches[i] = fresh
                    break
            else:
                branches.append(fresh)
            offer(board.text, board.accepted and is_done(board.text))
            changed.set()
            changed.clear()

        async def settle(candidate: Board) -> Board:
            """A placeholder with no goal is dropped; a goal with no placeholder
            gets one; several goals behind one placeholder each get their own."""

            for _ in range(4):
                _, spare, dear, broken = classify(candidate.messages)
                surplus = [l for l in (message_line(m) for m in spare) if l]
                idle = [g.line for g in candidate.goals if not g.text]
                if surplus or (idle and not dear and not broken):
                    candidate = await look(drop_lines(candidate.text, surplus or idle))
                    continue
                for goal in candidate.goals:
                    if goal.text.count("⊢") >= 2 and goal.key not in divided:
                        divided.add(goal.key)
                        apart = split_cursor(candidate.text, goal.text, candidate.index(goal))
                        if apart:
                            events.append({"stage": "split", "goals": goal.text.count("⊢")})
                            candidate = await look(apart)
                            break
                else:
                    return candidate
            return candidate

        failed_at = 0

        async def judge(base: Board, goal: Goal, block: str) -> tuple[Board | None, str]:
            """One edit at one goal, judged against the whole file. `failed_at`
            keeps the block-relative line of the first error, for the prefix cut."""

            nonlocal failed_at
            candidate, span = put(base.text, goal, block)
            nxt = await look(candidate, base)
            _, surplus, expensive, failures = classify(nxt.messages)
            lines = [l for l in (message_line(m) for m in failures) if l and span[0] <= l <= span[1]]
            failed_at = (min(lines) - span[0]) if lines else 0
            if any("TIMEOUT" in str(m.get("data")) for m in failures):
                # Measured on putnam_2018_a1: a timed-out check cost 120s plus a
                # container restart, and the prefix cut then paid it again.
                return None, TIMED_OUT
            if expensive and not failures:
                return None, BUDGET_RETRY
            if not failures and nxt.ms - base.ms > SLOW_STEP_MS:
                events.append({"stage": "slow", "ms": nxt.ms, "was": base.ms})
                return None, (f"that step makes the file take {nxt.ms // 1000}s to "
                              f"check, up from {base.ms // 1000}s; every later step "
                              "pays that. Use a cheaper tactic: a targeted rw or "
                              "exact, not simp with a wide lemma set or decide")
            if failures or expensive:
                # Every other open goal is an `unsolved goals` error too; the
                # model is told about its own step, not the rest of the board.
                own = [m for m in nxt.messages
                       if m in failures or m in expensive or in_span(m, span)]
                text = format_messages(own)[:FEEDBACK_CHARS]
                return None, f"{text}\n{notes_for(text)}".strip()
            if unreachable(nxt.messages, nxt.text, -1):
                return None, ("that step left a goal open inside a branch nothing "
                              "can get back to. A step that splits the goal gives "
                              "every branch its own `sorry`, or closes it outright")
            if any(in_span(m, span) for m in surplus):
                return None, ("there are no goals left where that step was written: "
                              "the goal was already closed above it")
            left = [g for g in nxt.goals if span[0] <= g.line <= span[1]]
            if left and all(g.text == goal.text for g in left):
                return None, "that step left the goal exactly as it was"
            if any(g.text.count("✝") > goal.text.count("✝") for g in left):
                # Measured on p10: `have h2 ...` accepted 18 times over, each one
                # shadowing the last, and the goal text never the same twice.
                return None, ("that step re-declared a name the context already "
                              "has (Lean shows the old one as `h✝`); use the "
                              "existing hypothesis instead of stating it again")
            if any(target_of(g.text) == "False" and target_of(goal.text) != "False"
                   and hyp_count(g.text) <= hyp_count(goal.text) for g in left):
                # Measured on rmo_2001_2: a wrong witness left `hp : Nat.Prime 3,
                # hq : Nat.Prime 11 ⊢ False` and 14 turns went into it.
                return None, ("that step turned the goal into `False` without adding "
                              "a hypothesis, so the context is still consistent and "
                              "`False` cannot be proved: the witness, rewrite or case "
                              "was wrong. Undo it and choose again")
            if left and max(inflated(goal.text, g.text) for g in left) >= INFLATION:
                # Measured on rmo_2001_2, p09 and rmo_2000_2 (5 runs): a rewrite
                # `at *` unfolded a variable in every hypothesis and both models
                # then worked on the unfolded form for the rest of the run.
                return None, ("that step made the existing hypotheses more than "
                              f"{INFLATION:g}× larger without closing the goal (a rewrite "
                              "unfolded a variable everywhere). Rewrite only the "
                              "hypothesis you need, or state the fact you want as a `have`")
            if any(META.search(target_of(g.text)) for g in left):
                # Measured on rmo_2000_2: `apply lt_irrefl _` left `⊢ Type ?u.350`
                # and `⊢ Preorder ?α`; each got a sorry and 30 turns, six deep.
                return None, ("that step left a goal Lean could not infer (`Type ?u`, "
                              "`?α`): an `apply` with `_` for arguments it cannot fill. "
                              "Give the term in full, e.g. `exact absurd h1 (not_lt.mpr h2)`")
            if any(len(VACUOUS.findall(g.text)) > len(VACUOUS.findall(goal.text)) for g in left):
                # Measured on p09: `simp ... at h ⊢` left `h : True ⊢ False`, Lean
                # had no complaint, and five turns went into a goal that was dead.
                return None, ("that step turned a hypothesis into `True` (or `Type`), "
                              "which throws the fact away; rewrite without `at h`, "
                              "or use the fact instead of simplifying it")
            return nxt, ""

        async def audit(author: str, base: Board, nxt: Board) -> str:
            """Every statement a step writes is tried against a witness: Lean
            states it, the auditor names values, Lean checks that they satisfy
            every hypothesis and break it. The refutation, or "" to let it in."""

            # Measured over 12 audits: a narrating model names values that violate
            # a hypothesis every time, at ~9 s; the other answers in ~1.4 s.
            other = next((m for m in models if m != author and not narrates(m)),
                         next((m for m in models if not narrates(m)),
                              next((m for m in models if m != author), author)))
            had = {g.key for g in base.goals}
            lines = nxt.text.split("\n")
            # Measured on putnam_2020_a2: a false `have` with a proof body had only
            # its residue audited. The claim is audited whatever the body says.
            known: dict[str, dict[str, str]] = {}
            subjects: list[dict[str, Any]] = []
            for i, ln in enumerate(lines):
                head = HAVE_HEAD.match(ln)
                decl = owner(nxt.text, i + 1) if head else ""
                claim = " ".join(claim_of(head.group(2).strip()).split()) if head else ""
                if not decl or not claim:
                    continue
                if decl not in known:
                    known[decl] = stated_facts(base.text, decl)
                if claim in known[decl]:
                    continue
                subjects.append({"key": (decl, "have " + claim), "decl": decl, "at": i,
                                 "what": head.group(2).strip(), "claim": claim})
            covered = {s["at"] for s in subjects}
            for g in nxt.goals:
                # `⊢ False` is provable only in an inconsistent context, so a witness
                # for the context alone proves the branch dead. Measured on p09: a
                # satisfiable `⊢ False` held both models for the rest of the run.
                dead_end = target_of(g.text) == "False"
                if (g.key in had or not g.text or META.search(target_of(g.text))
                        or not (dead_end or is_stated(lines, g))
                        or enclosing_have(lines, g)[0] in covered):
                    continue
                subjects.append({"key": g.key, "decl": g.decl, "goal": g, "what": "",
                                 "claim": ""})
            for sub in subjects:
                if audited.get(sub["key"]):
                    return audited[sub["key"]]
            subjects = [sub for sub in subjects if sub["key"] not in audited]
            if not subjects or not can_ask():
                return ""
            goals = [sub for sub in subjects if "goal" in sub]
            haves = [sub for sub in subjects if "at" in sub]
            if goals:
                said_ = statements((await services.lean.check_file(
                    extract_file(nxt.text, [sub["goal"] for sub in goals]),
                    timeout_s=check_timeout_s(nxt.ms))).messages)
                for sub in goals:
                    sub["stmt"] = said_.get(sub["goal"].line, "")
            if haves:
                text, where = have_extract_file(lines, [sub["at"] for sub in haves])
                said_ = statements((await services.lean.check_file(
                    text, timeout_s=check_timeout_s(nxt.ms))).messages)
                for sub in haves:
                    sub["stmt"] = said_.get(where.get(sub["at"], -1), "")
            # Definitions only: a hoisted lemma's proof would be paid again.
            roots = root_names(nxt.text)
            first = proof_span(nxt.text, roots[0]) if roots else None
            prefix = nxt.text[:first[0]] if first else ""
            for sub in subjects:
                sub["parsed"] = split_statement(sub["stmt"]) if sub.get("stmt") else None
            asked = [sub for sub in subjects if sub["parsed"]]
            replies = await asyncio.gather(*(self._call(
                other, audit_prompt(sub["stmt"], prefix.replace("import Mathlib", "")),
                AUDIT_TOKENS, services, ledger, system=AUDIT_SYSTEM) for sub in asked))
            for sub in subjects:
                audited[sub["key"]] = ""
                verdict, values = "unstated", {}
                target = sub["claim"] or target_of(sub["goal"].text)
                if sub["parsed"]:
                    groups, target = sub["parsed"]
                    reply, stopped = replies[asked.index(sub)]
                    names = {n for grp in groups for n in binder_names(grp)}
                    given = read_witness(reply)
                    values = {n: v for n, v in (given or {}).items() if n in names}
                    verdict = "unverified"
                    if given is None and stopped != "length" and "holds" in reply:
                        verdict = "holds"
                    if values or not names:
                        check = await services.lean.check_file(
                            witness_file(prefix, groups, values, target),
                            timeout_s=CHECK_TIMEOUT_FLOOR_S)
                        if check.accepted:
                            verdict = "refuted"
                events.append({"kind": "audit", "by": other, "goal": target[:100],
                               "verdict": verdict, "values": values})
                if verdict == "refuted":
                    stmt = sub["what"] or f"⊢ {target}"
                    if sub["claim"]:
                        withdrawn.setdefault(sub["decl"], []).append(claim_of(sub["what"]))
                    at = ", ".join(f"{n} = {v}" for n, v in values.items())
                    audited[sub["key"]] = (
                        f"`{stmt}` is false, so the step was not posted: with {at} every "
                        "hypothesis in scope holds and it fails (Lean checked this). Do "
                        "not restate it; state a fact that is true at those values too")
                    return audited[sub["key"]]
            return ""

        async def advance(base: Board, goal: Goal, block: str,
                          author: str) -> tuple[Board | None, str]:
            """A step, then its prefixes, then `exact?` in place of a bad proof."""

            nonlocal raised
            nxt, why = await judge(base, goal, block)
            if nxt is not None:
                bad = await audit(author, base, nxt)
                if bad:
                    return None, bad
            if nxt is None and why not in (BUDGET_RETRY, TIMED_OUT):
                # The first error's line says where to cut; one check instead of
                # eight. Measured: 3.7 checks per model call, most of them here.
                cuts = prefixes(block)
                guided = [c for c in cuts if c.count("\n") + 1 <= max(failed_at, 1)]
                order = guided[:1] + [c for c in cuts if c not in guided[:1]]
                tried = 0
                while order and tried < 3:
                    shorter = order[0]
                    tried += 1
                    nxt, _ = await judge(base, goal, shorter)
                    if nxt is not None:
                        events.append({"kind": "prefix", "by": author,
                                       "lines": shorter.count("\n") + 1})
                        return nxt, ""
                    order = order[len(order) // 2 + 1:] if len(order) > 1 else []
                retry = hand_to_search(block)
                if retry != block:
                    nxt, _ = await judge(base, goal, retry)
                    events.append({"kind": "search-retry", "by": author,
                                   "accepted": nxt is not None})
            if nxt is None and why == BUDGET_RETRY and not raised:
                raised = True
                lifted = await look(insert_preamble(base.text, RAISED_BUDGETS))
                moved = lifted.find(goal.key)
                if moved:
                    nxt, why = await judge(lifted, moved, block)
            if nxt is None and why == BUDGET_RETRY:
                why = ("the step exceeded Lean's elaboration budget even at a "
                       "raised budget; make it cheaper")
            return nxt, why

        async def sweep(goal: Goal) -> bool:
            """The free closers, once per goal. (`exact?` used to follow: measured
            1 of 51 goals closed over 24 runs, and a slow one restarts the container.)"""

            base = board
            block = tagged_closers(cocktail)
            nxt, _ = await judge(base, goal, block)
            events.append({"kind": "closers", "by": "harness", "accepted": nxt is not None})
            if nxt is None:
                return False
            tactic = fired_closer(nxt.messages, put(base.text, goal, block)[1], cocktail)
            flat = await look(put(base.text, goal, tactic)[0]) if tactic else None
            if flat is not None and flat.find(goal.key) is None and not any(
                    classify(flat.messages)[2:]):
                nxt = flat
            events.append({"kind": "collapse", "tactic": tactic, "accepted": nxt is flat})
            await commit(nxt)
            return True

        async def take_back(author: str, goal: Goal) -> None:
            """The `have` this goal is the body of comes off the board, with the
            rest of its block; the goal it was posted on is told why."""

            fresh, statement = withdraw(board.text, goal)
            if not fresh:
                return
            events.append({"kind": "withdraw", "by": author, "have": statement[:120],
                           "tries": tries.get(goal.key, 0)})
            withdrawn.setdefault(goal.decl, []).append(statement)
            await commit(await look(fresh))
            back = next((g for g in reversed(board.goals) if g.decl == goal.decl
                         and g.line <= goal.line), None)
            if back is not None:
                said[back.key] = Feedback(
                    author, f"`{statement}` was posted here as a `have` and withdrawn "
                    f"after {WITHDRAW_AFTER} failed attempts to prove it. The board is "
                    "back to before it. Do not restate that fact; prove this goal "
                    "another way, or through facts that are easier to prove", "withdrawn")

        async def lift_and_advance(base: Board, goal: Goal, block: str,
                                   author: str) -> tuple[Board | None, str]:
            """A fact posted with `sorry` inside a `have` goes above the outermost
            `have`: facts live at the shallowest scope. Measured on rmo_2000_2:
            skeletons nested 7 deep, 25 open goals, withdraw never firing."""

            lines = base.text.split("\n")
            chain = enclosing_chain(lines, goal)
            facts, rest = split_facts(block)
            if not chain or not facts:
                return await advance(base, goal, block, author)
            known = stated_facts(base.text, goal.decl)
            fresh, dup = [], []
            for f in facts:
                head = HAVE_HEAD.match(f.split("\n")[0])
                claim = " ".join(claim_of(head.group(2).strip()).split())
                (dup if claim in known else fresh).append((f, known.get(claim)))
            if dup and not fresh and not rest:
                names = ", ".join(f"`{n}`" for _, n in dup)
                return None, (f"every fact in that step is already on the board ({names}); "
                              "prove this goal from those facts, or close it directly")
            outer, head = chain[-1]
            lifted = [reindent(f, head.group(1)) for f, _ in fresh]
            text = "\n".join(lines[:outer] + lifted + lines[outer:])
            shift = sum(f.count("\n") + 1 for f in lifted)
            moved = Goal(goal.line + shift, goal.indent, goal.decl, goal.text)
            staged = Board(text, base.goals, base.messages, base.accepted, base.bid, base.ms)
            if rest:
                nxt, why = await advance(staged, moved, rest, author)
            else:
                nxt, why = await look(text, base), ""
                if classify(nxt.messages)[3]:
                    nxt, why = None, format_messages(classify(nxt.messages)[3])[:FEEDBACK_CHARS]
                elif nxt is not None:
                    bad = await audit(author, base, nxt)
                    if bad:
                        nxt, why = None, bad
            if nxt is None:
                return None, (why + f"\n(a fact stated inside `{head.group(2).strip()[:60]}` "
                              "is posted before that `have`, at the top of the proof; it can "
                              "only use the theorem's variables and the facts above it)")
            events.append({"kind": "lifted", "by": author, "facts": len(lifted),
                           "dup": len(dup), "from_depth": len(chain)})
            if dup:
                said[goal.key] = Feedback(author, "already on the board: " + ", ".join(
                    f"`{n}`" for _, n in dup), "lifted")
            return nxt, ""

        async def apply(author: str, goal: Goal, edits: list[Edit]) -> bool:
            """Every edit a reply asked for, each against the board as it stands."""

            took = False
            for edit in edits:
                here = board.find(goal.key)
                if edit.kind == "probe":
                    printed = await self._probe(State(text=board.text), edit.body, services)
                    said[goal.key] = Feedback(author, printed, "probe")
                    events.append({"kind": "probe", "by": author, "printed": printed[:80]})
                    continue
                if edit.kind == "drop":
                    events.append({"kind": "drop", "by": author, "name": edit.name})
                    said[goal.key] = Feedback(
                        author, f"`{edit.name}` is already declared; work the goal "
                        "you were shown, do not restate it", "rejected")
                    tries[goal.key] = tries.get(goal.key, 0) + 1
                    continue
                if edit.kind == "step":
                    if here is None:
                        events.append({"kind": "stale", "by": author})
                        continue
                    if (here.key, edit.body) in refused:
                        # Measured on p10: five byte-identical replies in a row.
                        events.append({"kind": "repeat", "by": author})
                        repeated.add((here.key, author))
                        said[goal.key] = Feedback(
                            author, "that is byte for byte the step already rejected "
                            "on this goal; Lean will say the same thing. Try a "
                            "different route: " + said[goal.key].text[:600]
                            if goal.key in said else "that step was already rejected here")
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    # Measured on p09: a substring match locked a worker out for 19
                    # min once `n % 3 = 0` was withdrawn and the goal read `⊢ n % 3 = 0`.
                    # Only a `have` stating the claim again is a restatement.
                    if restates(edit.body, withdrawn.get(here.decl, ())):
                        events.append({"kind": "restated", "by": author})
                        said[goal.key] = Feedback(author, "that step restates a fact "
                                                  "already withdrawn from this declaration")
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    present = proved_facts(board.text, here)
                    if restates(edit.body, present):
                        # Measured on p09: the same claim proved twice in one declaration.
                        names = [present[c] for c in present if restates(edit.body, [c])]
                        events.append({"kind": "restated", "by": author, "of": names[:3]})
                        said[goal.key] = Feedback(author, "that step states a fact already "
                                                  "on the board as " + ", ".join(f"`{n}`" for n in names[:3])
                                                  + "; use it, do not prove it again")
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    nxt, why = await lift_and_advance(board, here, edit.body, author)
                    if nxt is None:
                        refused.add((here.key, edit.body))
                    events.append({"kind": "step", "by": author, "accepted": nxt is not None})
                    if nxt is None:
                        said[goal.key] = Feedback(author, why)
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    await commit(nxt)
                    took = True
                    continue
                if edit.kind == "hoist":
                    lifted = await look(insert_above(board.text, first_graded, edit.block))
                    kept = not classify(lifted.messages)[3]
                    # Measured on putnam_2020_a2: a hoisted lemma was false at j = 0;
                    # its statement is audited like a `have` before it enters the file.
                    bad = await audit(author, board, lifted) if kept else ""
                    kept = kept and not bad
                    events.append({"kind": "lemma", "by": author, "name": edit.name,
                                   "accepted": kept})
                    if not kept:
                        said[goal.key] = Feedback(
                            author, bad or format_messages(lifted.messages)[:FEEDBACK_CHARS])
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    await commit(lifted)
                    took = True
                    fresh = next((g for g in board.goals if g.decl == edit.name), None)
                    if fresh and edit.body.strip():
                        nxt, why = await advance(board, fresh, edit.body, author)
                        events.append({"kind": "step", "by": author, "accepted": nxt is not None})
                        if nxt is not None:
                            await commit(nxt)
                        else:
                            said[fresh.key] = Feedback(author, why)
                    continue
                if edit.kind == "prove":
                    # The whole proof of a named declaration replaces what it had.
                    # Measured on p09: appended, it doubled its own opening; dropped,
                    # it was the best turn of the run.
                    fresh_text, at = restate(board.text, edit.name)
                    if at < 0:
                        continue
                    opened = await look(fresh_text)
                    target = opened.goals[at] if at < len(opened.goals) else None
                    events.append({"kind": "route", "by": author, "to": edit.name})
                    if target is None:
                        continue
                    nxt, why = await advance(opened, target, edit.body, author)
                    if nxt is None and here is not None and edit.name == here.decl:
                        # The header was an echo and the body continues from here.
                        nxt, why = await advance(board, here, edit.body, author)
                    events.append({"kind": "step", "by": author, "accepted": nxt is not None})
                    if nxt is None:
                        said[goal.key] = Feedback(author, why)
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    await commit(nxt)
                    took = True
            return took

        def pick(model: str) -> tuple[Board, Goal] | None:
            """The best branch's least-tried unclaimed goal; with none unclaimed
            anywhere, one the other model holds, so a 158s reply does not idle
            the fast model. Measured on p09: 4 minutes of 20 went that way."""

            options = []
            for rank, b in enumerate(sorted(branches, key=lambda b: b.score)):
                for g in b.goals:
                    if g.text and claimed.get(g.key) != model:
                        options.append(((g.key, model) in repeated, g.key in claimed, rank,
                                        tries.get(g.key, 0) >= LAST_IN_LINE,
                                        tries.get(g.key, 0), g.line, b, g))
            if not options:
                return None
            best = min(options, key=lambda o: o[:6])
            return best[6], best[7]

        async def unstick() -> None:
            """Every goal last in line: the worst one's declaration starts over."""

            worst = max(board.goals, key=lambda g: tries.get(g.key, 0), default=None)
            if worst is None or not worst.decl or restated.get(worst.decl, 0) >= MAX_RESTATES:
                return
            restated[worst.decl] = restated.get(worst.decl, 0) + 1
            fresh_text, _ = restate(board.text, worst.decl)
            events.append({"stage": "restate", "decl": worst.decl,
                           "tries": tries.get(worst.key, 0)})
            await commit(await look(fresh_text))

        def prompt_for(goal: Goal, model: str, skeleton: bool = False) -> str:
            source, line = view(*render(board.text, board.index(goal))[:1], goal.decl)
            parts = [f"Problem: {problem.description}".strip(),
                     "File:\n" + source[-FILE_CHARS:],
                     "What Lean reports as open, with its hypotheses. The first goal "
                     f"is the active one, at `skip` on line {line}:\n"
                     f"{goal.text[:GOAL_CHARS]}"]
            if plans.get(goal.key):
                parts.append("A mathematician was asked how to prove this goal and "
                             f"answered:\n{plans[goal.key]}")
            if said.get(goal.key):
                parts.append(f"{said[goal.key].lead(model)}:\n{said[goal.key].text}")
            if skeleton:
                # Measured on rmo_2001_2: the plan was right at t=173 and both
                # models then tried to write all of it in one reply, 37 times
                # past the token cap. The plan goes on the board as statements.
                parts.append("Write the plan as a skeleton: one `have` per fact "
                             "in the order the plan uses them, each with the "
                             "statement in full and the body `:= by sorry`, then "
                             "the one tactic line that closes the goal from those "
                             "facts. Do not prove any fact here; each becomes a "
                             "goal of its own.")
            parts.append("Reply with one ```lean code block containing only tactic "
                         "lines, and nothing before or after it. No explanation.")
            return "\n\n".join(parts)

        async def worker(model: str) -> None:
            nonlocal finished
            idle, faults = 0, 0
            while time_left() > 0 and can_ask() and not finished:
                try:
                    if await turn(model):
                        idle = 0
                    else:
                        idle += 1
                        if idle > 3 and not claimed:
                            events.append({"stage": "stop", "note": "no goal left to work on"})
                            return
                        try:
                            await asyncio.wait_for(changed.wait(), IDLE_WAIT_S)
                        except asyncio.TimeoutError:
                            pass
                except (BudgetExceeded, BudgetAccountingError, LeanRuntimeError, LLMCallError):
                    raise
                except Exception as exc:  # noqa: BLE001 - one bad turn must not zero the problem
                    faults += 1
                    events.append({"stage": "worker_error", "by": model,
                                   "error": f"{type(exc).__name__}: {exc}"[:200]})
                    if faults >= 3:
                        return

        async def turn(model: str) -> bool:
            """One turn for one worker: False when there was no goal to take."""

            nonlocal finished
            if True:
                async with lock:
                    if any(b.accepted and is_done(b.text) for b in branches):
                        finished = True
                        return True
                    picked = pick(model)
                    goal = picked[1] if picked else None
                    if picked:
                        focus(picked[0])
                    base = board
                    if goal is not None and goal.key not in swept:
                        swept.add(goal.key)
                        if await sweep(goal):
                            return True
                    if goal is None:
                        if not claimed and board.goals and all(
                                tries.get(g.key, 0) >= LAST_IN_LINE for g in board.goals):
                            await unstick()
                    else:
                        claimed.setdefault(goal.key, model)
                        wants_plan = (tries.get(goal.key, 0) >= PLAN_AFTER
                                      and not plans.get(goal.key))
                        ask = prompt_for(goal, model)
                if goal is not None and wants_plan:
                    other = next((m for m in models if m != model), model)
                    plan = await self._ask_plan(
                        problem, State(text=board.text, goal=goal.text),
                        services, ledger, other)
                    async with lock:
                        plans[goal.key] = plan
                        events.append({"kind": "plan", "by": other, "chars": len(plan)})
                        now = live(base.bid)
                        moved = now.find(goal.key) if now else None
                        if moved:
                            focus(now)
                            goal = moved
                        ask = prompt_for(goal, model, skeleton=True) if moved else ""
                        if ask:
                            events.append({"kind": "skeleton", "by": model})
                    if not ask:
                        async with lock:
                            claimed.pop(goal.key, None)
                        return True
                if goal is None:
                    return False
                task = asyncio.ensure_future(
                    self._call(model, ask, step_tokens(model), services, ledger, system=BOARD_SYSTEM))
                loose.append(task)
                try:
                    reply, why = await task
                finally:
                    loose.remove(task)
                async with lock:
                    if claimed.get(goal.key) == model:
                        claimed.pop(goal.key, None)
                    if why == "length":
                        reply = salvage(reply)
                        kept = reply.count("\n") + 1 if reply else 0
                        events.append({"kind": "cut", "by": model, "kept": kept})
                        if not kept:
                            said[goal.key] = Feedback(model, said[goal.key].text
                                                      if goal.key in said else "nothing yet", "cut")
                            tries[goal.key] = tries.get(goal.key, 0) + 1
                            return True
                    now = live(base.bid)
                    here = now.find(goal.key) if now else None
                    if here is not None:
                        focus(now)
                    elif base.find(goal.key) is not None and len(branches) < BEAM + 1:
                        # The goal moved on under this reply. Judged against the
                        # file it was asked about, an accepted answer is a second
                        # way forward, and a second way is a branch, not waste.
                        nonlocal next_bid
                        fork = Board(base.text, list(base.goals), list(base.messages),
                                     base.accepted, next_bid)
                        next_bid += 1
                        sound[fork.bid] = sound.get(base.bid, base.text)
                        branches.append(fork)
                        focus(fork)
                        here = fork.find(goal.key)
                        edits = interpret(reply, board, here, graded)
                        took = await apply(model, here, edits) if edits else False
                        if took and live(fork.bid):
                            events.append({"stage": "fork", "from": base.bid, "to": fork.bid,
                                           "goal": goal.text[:60]})
                            prune()
                        else:
                            if live(fork.bid):
                                branches.remove(live(fork.bid))
                            events.append({"kind": "stale", "by": model})
                        return True
                    if here is None:
                        events.append({"kind": "stale", "by": model})
                        return True
                    edits = interpret(reply, board, here, graded)
                    if not edits:
                        events.append({"kind": "empty", "by": model})
                        said[goal.key] = Feedback(model, said[goal.key].text
                                                  if goal.key in said else "nothing yet", "empty")
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        return True
                    await apply(model, here, edits)
                    still = board.find(goal.key)
                    if still is not None and tries.get(goal.key, 0) >= WITHDRAW_AFTER:
                        await take_back(model, still)
                return True

        try:
            cocktail = await usable_cocktail(services)
            for candidate in sweep_files(problem.challenge, cocktail) + split_files(
                    problem.challenge, cocktail):
                if time_left() <= 0:
                    break
                check = await services.lean.check_file(candidate)
                if check.accepted and not scoring_faults(candidate, names, problem.challenge):
                    events.append({"stage": "sweep", "accepted": True})
                    won = await deliver(candidate, "deterministic_sweep")
                    if won:
                        return won
                    offer(candidate, True)
                    return result(candidate, "deterministic_sweep", True)

            if graded_theorems(problem.challenge) > 1 and can_ask():
                text = await self._share(problem, text, services, ledger, events)
            if definition_slots(text) and can_ask():
                text = await self._define(problem, text, services, ledger, events)
            if names and can_ask():
                text = await self._resolve_answers(
                    problem, text, names, services, ledger, events)

            board = Board(text, bid=0)
            await commit(await look(text))
            tasks = [asyncio.ensure_future(worker(m)) for m in models]
            try:
                await asyncio.gather(*tasks)
            finally:
                finished = True
                await asyncio.wait(tasks, timeout=LOOSE_DRAIN_S)

            done = [b for b in branches if b.accepted and is_done(b.text)]
            if done:
                won = await deliver(done[0].text, "board_loop")
                if won:
                    return won
            if branches:
                board = min(branches, key=lambda b: b.score)
            offer(board.text, False)
            return result(best, "best_effort", False)
        except (BudgetExceeded, BudgetAccountingError, LeanRuntimeError, LLMCallError) as exc:
            events.append({"stage": "abort", "error": type(exc).__name__})
            return result(best, "aborted", False)
        finally:
            if loose:
                await asyncio.wait(list(loose), timeout=LOOSE_DRAIN_S)


def create_agent() -> BoardAgent:
    return BoardAgent()
