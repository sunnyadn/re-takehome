"""A board of open goals, each known by its content, two models working two
of them at once; Lean judges every edit against the whole file. The file is
still the proof; a reply is read once, as a proof of whatever it names."""


from __future__ import annotations

import asyncio
import time
from dataclasses import dataclass, field
from typing import Any, Sequence

from re_harness import AgentResult, Problem, Services
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
    BUDGET_RETRY,
    FILE_CHARS,
    GOAL_CHARS,
    LOOSE_DRAIN_S,
    MAX_PREFIXES,
    RAISED_BUDGETS,
    SLOW_COMPILE_MS,
    STEP_TOKENS,
    Feedback,
    FrameworkAgent,
    State,
    is_probe,
    notes_for,
    screen_step,
)

# Two rejections on a goal buy it a plan from the other model, as before.
PLAN_AFTER = 2
# A goal this many rejections deep is still open, only last in line. Time and
# money are the exits; a goal is never declared hopeless by count alone.
LAST_IN_LINE = 6
# When every goal is last in line, the declaration holding the worst of them
# goes back to its statement, this many times at most.
MAX_RESTATES = 2
# A worker with no goal to take waits this long for the board to change.
IDLE_WAIT_S = 2.0


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

    def find(self, key: tuple[str, str]) -> Goal | None:
        return next((g for g in self.goals if g.key == key), None)

    def index(self, goal: Goal) -> int:
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


def put(text: str, goal: Goal, block: str, trailing: bool = True) -> tuple[str, tuple[int, int]]:
    """The block where the goal's placeholder is, and the lines it now covers."""

    lines = text.split("\n")
    body = reindent(normalise_steps(block), goal.indent)
    if trailing:
        body = f"{body}\n{goal.indent}sorry"
    lines[goal.line - 1] = body
    return "\n".join(lines), (goal.line, goal.line + body.count("\n"))


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

    block = screen_step(reply)
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
        sound = text

        async def look(candidate: str) -> Board:
            check = await services.lean.check_file(render_all(candidate))
            return read_board(candidate, check.messages, check.accepted)

        async def commit(candidate: Board) -> None:
            """Make a board current, after its own housekeeping."""

            nonlocal board, sound
            board = await settle(candidate)
            _, _, dear, broken = classify(board.messages)
            if broken or dear:
                if board.text != sound:
                    events.append({"stage": "repair",
                                   "why": "cost" if dear and not broken else "error",
                                   "said": format_messages(broken or dear)[:300]})
                    board = await look(sound)
            else:
                sound = board.text
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

        async def judge(base: Board, goal: Goal, block: str) -> tuple[Board | None, str]:
            """One edit at one goal, judged against the whole file."""

            candidate, span = put(base.text, goal, block)
            nxt = await look(candidate)
            _, surplus, expensive, failures = classify(nxt.messages)
            if expensive and not failures:
                return None, BUDGET_RETRY
            if failures or expensive:
                text = format_messages(nxt.messages)[:FEEDBACK_CHARS]
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
            return nxt, ""

        async def advance(base: Board, goal: Goal, block: str,
                          author: str) -> tuple[Board | None, str]:
            """A step, then its prefixes, then `exact?` in place of a bad proof."""

            nonlocal raised
            nxt, why = await judge(base, goal, block)
            if nxt is None and why != BUDGET_RETRY:
                for shorter in prefixes(block)[:MAX_PREFIXES]:
                    nxt, _ = await judge(base, goal, shorter)
                    if nxt is not None:
                        events.append({"kind": "prefix", "by": author,
                                       "lines": shorter.count("\n") + 1})
                        return nxt, ""
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

            for kind, block in (("closers", sweep_body(cocktail)), ("search", "exact?")):
                nxt, _ = await judge(board, goal, block)
                events.append({"kind": kind, "by": "harness", "accepted": nxt is not None})
                if nxt is not None:
                    if kind == "closers":
                        state = await self._collapse_last(
                            State(text=nxt.text, focus=0), services)
                        nxt = await look(state.text)
                    await commit(nxt)
                    return True
            return False

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
                    continue
                if edit.kind == "step":
                    if here is None:
                        events.append({"kind": "stale", "by": author})
                        continue
                    nxt, why = await advance(board, here, edit.body, author)
                    events.append({"kind": "step", "by": author, "accepted": nxt is not None})
                    if nxt is None:
                        said[goal.key] = Feedback(author, why)
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    await commit(nxt)
                    took = True
                    continue
                if edit.kind == "hoist":
                    lifted = await look(insert_preamble(board.text, edit.block))
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

        def pick(model: str) -> Goal | None:
            """The least-tried unclaimed goal, in file order among equals."""

            free = [g for g in board.goals if g.key not in claimed and g.text]
            if not free:
                return None
            return min(free, key=lambda g: (tries.get(g.key, 0) >= LAST_IN_LINE,
                                            tries.get(g.key, 0), g.line))

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

        def prompt_for(goal: Goal, model: str) -> str:
            source, line = render(board.text, board.index(goal))
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
            parts.append("Reply with one ```lean code block containing only tactic "
                         "lines, and nothing before or after it. No explanation.")
            return "\n\n".join(parts)

        async def worker(model: str) -> None:
            nonlocal finished
            idle = 0
            while time_left() > 0 and can_ask() and not finished:
                async with lock:
                    if board.accepted and is_done(board.text):
                        finished = True
                        return
                    goal = pick(model)
                    if goal is not None and goal.key not in swept:
                        swept.add(goal.key)
                        if await sweep(goal):
                            continue
                    if goal is None:
                        if not claimed and board.goals and all(
                                tries.get(g.key, 0) >= LAST_IN_LINE for g in board.goals):
                            await unstick()
                    else:
                        claimed[goal.key] = model
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
                        ask = prompt_for(goal, model) if board.find(goal.key) else ""
                    if not ask:
                        async with lock:
                            claimed.pop(goal.key, None)
                        continue
                if goal is None:
                    idle += 1
                    if idle > 3 and not claimed:
                        events.append({"stage": "stop", "note": "no goal left to work on"})
                        return
                    try:
                        await asyncio.wait_for(changed.wait(), IDLE_WAIT_S)
                    except asyncio.TimeoutError:
                        pass
                    continue
                idle = 0
                task = asyncio.ensure_future(
                    self._call(model, ask, STEP_TOKENS, services, ledger))
                loose.append(task)
                try:
                    reply, why = await task
                finally:
                    loose.remove(task)
                async with lock:
                    claimed.pop(goal.key, None)
                    if why == "length":
                        events.append({"kind": "cut", "by": model})
                        said[goal.key] = Feedback(model, said[goal.key].text
                                                  if goal.key in said else "nothing yet", "cut")
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    here = board.find(goal.key)
                    if here is None:
                        events.append({"kind": "stale", "by": model})
                        continue
                    edits = interpret(reply, board, here, graded)
                    if not edits:
                        events.append({"kind": "empty", "by": model})
                        said[goal.key] = Feedback(model, said[goal.key].text
                                                  if goal.key in said else "nothing yet", "empty")
                        tries[goal.key] = tries.get(goal.key, 0) + 1
                        continue
                    await apply(model, here, edits)

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

            await commit(await look(text))
            await asyncio.gather(*(worker(m) for m in models))

            if is_done(board.text):
                won = await deliver(board.text, "board_loop")
                if won:
                    return won
            offer(board.text, False)
            return result(best, "best_effort", False)
        except (BudgetExceeded, BudgetAccountingError, LeanRuntimeError) as exc:
            events.append({"stage": "abort", "error": type(exc).__name__})
            return result(best, "aborted", False)
        finally:
            if loose:
                await asyncio.wait(list(loose), timeout=LOOSE_DRAIN_S)


def create_agent() -> BoardAgent:
    return BoardAgent()
