"""A board of open goals, each known by its content, two models working two
of them at once; Lean judges every edit against the whole file. The file is
still the proof; a reply is read once, as a proof of whatever it names."""


from __future__ import annotations

import asyncio
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


CLOSER_TAG = re.compile(r"^closer (\d+)$")


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
        if not isinstance(m, dict) or m.get("severity") != "information":
            continue
        tag = CLOSER_TAG.match(str(m.get("data", "")).strip())
        line = message_line(m)
        if tag and line is not None and span[0] <= line <= span[1]:
            hits.append((line, int(tag.group(1))))
    return cocktail[max(hits)[1]] if hits else None


def withdraw(text: str, goal: Goal) -> tuple[str, str]:
    """The file with the `have` enclosing this goal, and the rest of its block,
    cut back to one `sorry`; the withdrawn statement second. ("", "") when the
    nearest shallower line above the goal is not a `have ... := by`."""
    lines = text.split("\n")
    i = goal.line - 1
    above = next((j for j in range(i - 1, -1, -1) if lines[j].strip()
                  and len(lines[j]) - len(lines[j].lstrip()) < len(goal.indent)), None)
    head = HAVE_HEAD.match(lines[above]) if above is not None else None
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


def put(text: str, goal: Goal, block: str, trailing: bool = True) -> tuple[str, tuple[int, int]]:
    """The block where the goal's placeholder is, and the lines it now covers."""

    lines = text.split("\n")
    body = reindent(normalise_steps(block), goal.indent)
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
        tries: dict[tuple[str, str], int] = {}
        said: dict[tuple[str, str], Feedback] = {}
        plans: dict[tuple[str, str], str] = {}
        swept: set[tuple[str, str]] = set()
        divided: set[tuple[str, str]] = set()
        restated: dict[str, int] = {}
        refused: set[tuple[tuple[str, str], str]] = set()
        withdrawn: dict[str, list[str]] = {}
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

        async def advance(base: Board, goal: Goal, block: str,
                          author: str) -> tuple[Board | None, str]:
            """A step, then its prefixes, then `exact?` in place of a bad proof."""

            nonlocal raised
            nxt, why = await judge(base, goal, block)
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
            """The free closers, then `exact?`, once per goal."""

            base = board
            for kind, block in (("closers", tagged_closers(cocktail)), ("search", "exact?")):
                nxt, _ = await judge(base, goal, block)
                events.append({"kind": kind, "by": "harness", "accepted": nxt is not None})
                if nxt is not None:
                    if kind == "closers":
                        tactic = fired_closer(nxt.messages, put(base.text, goal, block)[1], cocktail)
                        flat = await look(put(base.text, goal, tactic)[0]) if tactic else None
                        if flat is not None and flat.find(goal.key) is None and not any(
                                classify(flat.messages)[2:]):
                            nxt = flat
                        events.append({"kind": "collapse", "tactic": tactic,
                                       "accepted": nxt is flat})
                    await commit(nxt)
                    return True
            return False

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
                        said[goal.key] = Feedback(
                            author, "that is byte for byte the step already rejected "
                            "on this goal; Lean will say the same thing. Try a "
                            "different route: " + said[goal.key].text[:600]
                            if goal.key in said else "that step was already rejected here")
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    if any(w in edit.body for w in withdrawn.get(here.decl, ())):
                        events.append({"kind": "restated", "by": author})
                        said[goal.key] = Feedback(author, "that step restates a fact "
                                                  "already withdrawn from this declaration")
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    nxt, why = await advance(board, here, edit.body, author)
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
                    events.append({"kind": "lemma", "by": author, "name": edit.name,
                                   "accepted": kept})
                    if not kept:
                        said[goal.key] = Feedback(
                            author, format_messages(lifted.messages)[:FEEDBACK_CHARS])
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

            for shared in (False, True):
                for b in sorted(branches, key=lambda b: b.score):
                    free = [g for g in b.goals if g.text and (
                        g.key not in claimed if not shared else claimed.get(g.key) != model)]
                    if free:
                        return b, min(free, key=lambda g: (
                            tries.get(g.key, 0) >= LAST_IN_LINE, tries.get(g.key, 0), g.line))
            return None

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
                    self._call(model, ask, STEP_TOKENS, services, ledger, system=BOARD_SYSTEM))
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
