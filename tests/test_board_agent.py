import asyncio
import re
import time

from re_harness import Problem
from re_harness.lean import LeanCheck
from submission.config import Config
from submission.sweep import COCKTAIL
from submission.cells import CELL_PROBE
from submission.board_agent import BoardAgent
from submission.board.probes import PROBE, read_board, render_all
from submission.board.reply import interpret
from submission.board.types import Board, Goal
from tests.test_framework_loop import FakeServices, said

ONE = "import Mathlib\n\ntheorem demo : True := by\n  sorry\n"
TWO = ("import Mathlib\n\ntheorem demo : True := by\n  sorry\n\n"
       "theorem demo_b : True := by\n  sorry\n")
HEAD = re.compile(r"^\s*(?:theorem|lemma)\s+(\w+)")


class BoardLean:
    """Every `skip` reports its own goal, whose hypotheses are the `have`s above
    it in the same declaration. `exact key` closes when `key` is in scope."""

    states_goals = False   # a CellLean answers the probe's extract_goal too

    def __init__(self):
        self.sources: list[str] = []

    async def check_file(self, source, timeout_s=None):
        self.sources.append(source)
        if "vm_probe" in source:
            return LeanCheck(True, [], False, False, 1)
        if "Nearest that exist" in source:
            asked = re.findall(r'"([^"]+)"', source.split("wanted", 1)[1].split("\n", 1)[0])
            return LeanCheck(True, [{"severity": "info", "pos": {"line": 3}, "endPos": {"line": 3},
                                     "data": f"{n} is not a name. Nearest that exist:\n  "
                                             f"Nat.real_{n.split('.')[-1]} : ∀ n, True"}
                                    for n in asked], False, False, 1)
        messages, decl, haves, target_of_decl = [], "", [], ""
        for i, line in enumerate(source.split("\n"), start=1):
            head = HEAD.match(line)
            if head:
                decl, haves, target_of_decl = head.group(1), [], ""
                if decl.startswith("vm_cell_"):
                    # A cell's header carries the context it was stated with.
                    haves = re.findall(r"\((\w+) : P\)", line)
                    target_of_decl = re.match(r"\s*theorem \w+(?: \(.*\))? : (.+?) := by\s*$", line).group(1)
                continue
            body = line.strip()
            if body.startswith("have "):
                haves.append(body.split()[1])
            if body == "intro loc":
                haves.append("loc")
            if body.startswith("have ") and " loc" in body and \
                    not any(l.strip() == "intro loc" for l in source.split("\n")[:i - 1]):
                messages.append({"severity": "error", "pos": {"line": i - 1},
                                 "endPos": {"line": i - 1},
                                 "data": "Unknown identifier `loc`"})
            if re.match(r"exact gone\w*$", body) and body.split()[1] not in haves:
                messages.append({"severity": "error", "pos": {"line": i - 1},
                                 "endPos": {"line": i - 1},
                                 "data": f"Unknown identifier `{body.split()[1]}`"})
            if body.startswith("exact Nat."):
                messages.append({"severity": "error", "pos": {"line": i - 1},
                                 "endPos": {"line": i - 1},
                                 "data": f"Unknown constant `{body.split()[1]}`"})
            if decl and body.startswith(("first", "exact?", "linarith")) and "vm_cell_" not in body:
                messages.append({"severity": "error", "pos": {"line": i - 1},
                                 "endPos": {"line": i - 1},
                                 "data": "linarith failed to find a contradiction"})
            if body in ("skip", PROBE, CELL_PROBE):
                # An `exact` of a name in scope closes the block it is in: the
                # placeholders after it in that block have no goal (real Lean:
                # `skip` is silent there, the probe reports it).
                rows = source.split("\n")
                depth = len(line) - len(line.lstrip())
                closed = False
                for j in range(i - 2, -1, -1):
                    if HEAD.match(rows[j]) or (rows[j].strip() and
                                               len(rows[j]) - len(rows[j].lstrip()) < depth):
                        break
                    if len(rows[j]) - len(rows[j].lstrip()) == depth and \
                            any(rows[j].strip() == f"exact {h}" for h in haves) and \
                            not decl.startswith("stuck"):      # a `stuck_*` declaration never closes
                        closed = True
                        break
                if closed:
                    if body in (PROBE, CELL_PROBE):
                        messages.append({"severity": "error", "pos": {"line": i - 1},
                                         "endPos": {"line": i - 1},
                                         "data": "No goals to be solved"})
                    continue
                hyps = "".join(f"{h} : P\n" for h in haves)
                above = rows[i - 2].strip() if i > 1 else ""
                target = (above.split(":", 1)[1].split(":=")[0].strip()
                          if above.startswith("have ") and above.endswith(":= by")
                          else "False" if above == "exfalso"
                          else f"P {above.split()[1]}" if above.startswith("use ")
                          else target_of_decl or decl)
                # Lean reports the block's open goal on its `by`, spanning the
                # block: the nearest line above at a shallower indent.
                head_at = next((j for j in range(i - 2, -1, -1) if rows[j].strip() and
                                len(rows[j]) - len(rows[j].lstrip()) < depth), i - 2)
                messages.append({"severity": "error", "pos": {"line": head_at, "column": 2},
                                 "endPos": {"line": i - 1},
                                 "data": f"unsolved goals\n{hyps}⊢ {target}"})
                if body == CELL_PROBE and self.states_goals:
                    binders = " ".join(f"({h} : P)" for h in haves)
                    messages.append({"severity": "info", "pos": {"line": i - 1}, "endPos": {"line": i - 1},
                                     "data": f"theorem {decl}.extracted_1 {binders} : {target} := sorry"})
        errors = [m for m in messages if m["severity"] == "error"]
        return LeanCheck(not errors, messages, "sorry" in source, False, 1)


class YieldingLean(BoardLean):
    """A check that actually suspends, so a second worker can be scheduled.

    `BoardLean.check_file` has no await in its body, so awaiting it never
    yields and the two workers run strictly one after the other. A test about
    what two workers do to each other needs this instead. It is not the
    default: the stall tests drive their clock off the number of
    `time.monotonic` calls, and an extra suspension point changes that count."""

    async def check_file(self, source, timeout_s=None):
        await asyncio.sleep(0)
        return await super().check_file(source, timeout_s)


class CellLean(BoardLean):
    """BoardLean that also states every goal, so blocks get cells of their own."""

    states_goals = True


class ScriptLLM:
    """Replies chosen by who is asking; each model has its own queue."""

    def __init__(self, scripts: dict[str, list[str]], delay: dict[str, float] | None = None):
        self.scripts = {k: list(v) for k, v in scripts.items()}
        self.delay = delay or {}
        self.calls: list[tuple[str, str]] = []

    async def complete(self, *, model, messages, **kwargs):
        prompt = messages[-1]["content"]
        self.calls.append((model, prompt))
        self.systems = getattr(self, "systems", []) + [messages[0]["content"]]
        self.kwargs = getattr(self, "kwargs", []) + [dict(kwargs, model=model)]
        if self.delay.get(model):
            await asyncio.sleep(self.delay[model])
        if "competition mathematician" in messages[0]["content"]:
            self.plans = getattr(self, "plans", 0) + 1
            return said(f"Take the obvious route ({self.plans}).", 0.001)
        queue = self.scripts.get(model, [])
        reply = queue.pop(0) if queue else "have junk : True := by trivial"
        if isinstance(reply, tuple):
            return said(reply[0], 0.01, reply[1])
        return said(reply, 0.01)


def run(challenge, scripts, delay=None, lines=("model-a", "model-b"), time_limit=600.0):
    lean, llm = BoardLean(), ScriptLLM(scripts, delay)
    agent = BoardAgent(Config(lines=lines, budget_usd=1.0, time_limit_s=time_limit))
    problem = Problem(id="demo", description="prove it", challenge=challenge)
    started = time.monotonic()
    result = asyncio.run(agent.solve(problem, FakeServices(lean, llm)))
    return result, lean, llm, time.monotonic() - started


def test_two_workers_never_have_two_lean_checks_in_flight_at_once():
    # One container per problem, so a check cannot overlap a check whatever the
    # board does. The second worker is there to overlap model latency, and this
    # says so in a way that fails if a check ever escapes the board lock.
    # `YieldingLean` is what makes the assertion mean anything: `BoardLean`
    # never suspends, so nothing could overlap even if the lock were gone.
    class Counting(YieldingLean):
        def __init__(self):
            super().__init__()
            self.inside, self.most, self.n = 0, 0, 0

        async def check_file(self, source, timeout_s=None):
            self.inside += 1
            self.n += 1
            self.most = max(self.most, self.inside)
            try:
                return await super().check_file(source, timeout_s)
            finally:
                self.inside -= 1

    lean, llm = Counting(), ScriptLLM({m: ["trivial"] * 8 for m in ("model-a", "model-b")},
                                  {"model-a": 0.001, "model-b": 0.001})
    agent = BoardAgent(Config(lines=("model-a", "model-b"), budget_usd=1.0, time_limit_s=30.0))
    asyncio.run(agent.solve(Problem(id="demo", description="prove it", challenge=TWO),
                            FakeServices(lean, llm)))
    assert lean.n > 5, "the run did too little to mean anything: %d checks" % lean.n
    assert lean.most == 1, "two Lean checks overlapped: %d" % lean.most
    assert lean.inside == 0


def steps(result):
    return [e for e in result.metadata["events"] if e.get("kind") == "step"]


def test_every_placeholder_is_rendered_as_skip_at_once():
    assert render_all(TWO).count("skip") == 2 and "sorry" not in render_all(TWO)


def test_the_board_reads_one_goal_per_placeholder_with_its_own_context():
    text = ("import Mathlib\n\ntheorem demo : True := by\n  have k : True := by\n"
            "    sorry\n  sorry\n\ntheorem demo_b : True := by\n  sorry\n")
    from submission.contract import FileCoordinates
    check = asyncio.run(FileCoordinates(BoardLean()).check_file(render_all(text)))
    board = read_board(text, check.messages, check.accepted)
    assert [g.decl for g in board.goals] == ["demo", "demo", "demo_b"]
    assert [g.line for g in board.goals] == [5, 6, 9]
    assert board.goals[1].text == "k : P\n⊢ demo" and board.goals[2].text == "⊢ demo_b"


def test_a_reply_is_read_as_proofs_of_what_it_names():
    board = Board(TWO, [Goal(4, "  ", "demo", "⊢ demo"), Goal(7, "  ", "demo_b", "⊢ demo_b")])
    at = board.goals[0]
    assert [e.kind for e in interpret("```lean\nexact key\n```", board, at, ("demo",))] == ["step"]
    routed = interpret("theorem demo_b : True := by\n  exact key", board, at, ("demo",))
    assert [(e.kind, e.name, e.body) for e in routed] == [("prove", "demo_b", "exact key")]
    new = interpret("lemma helper (n : ℕ) :\n    n = n := by\n  rfl", board, at, ("demo",))
    assert new[0].kind == "hoist" and new[0].name == "helper" and new[0].body == "rfl"
    assert new[0].block.endswith(":= by\n  sorry")
    closed = Board(TWO.replace("theorem demo : True := by\n  sorry", "theorem demo : True := by\n  trivial"),
                   [Goal(7, "  ", "demo_b", "⊢ demo_b")])
    assert [e.kind for e in interpret("theorem demo : True := by\n  trivial",
                                      closed, closed.goals[0], ("demo",))] == ["drop"]


def test_two_models_work_two_goals_and_the_file_is_finished():
    # The shared-lemma question comes first and takes one reply from each line.
    result, lean, llm, _ = run(TWO, {
        "model-a": ["no", "have key : True := by trivial", "exact key"],
        "model-b": ["no", "have key : True := by trivial", "exact key"],
    })
    assert result.metadata["accepted_by_repl"] is True
    assert "sorry" not in result.solution
    assert {e["by"] for e in steps(result) if e["accepted"]} == {"model-a", "model-b"}


def test_a_slow_model_does_not_hold_the_fast_one_up():
    result, lean, llm, wall = run(TWO, {
        "model-a": ["no", "have key : True := by trivial", "exact key",
                    "have key : True := by trivial", "exact key"],
        "model-b": ["no", "have key : True := by trivial"],
    }, delay={"model-b": 0.6})
    assert result.metadata["accepted_by_repl"] is True
    # model-a's four turns did not wait behind model-b's 0.6s reply.
    assert wall < 1.5, wall


def test_a_whole_proof_of_another_open_declaration_replaces_its_body():
    result, lean, llm, _ = run(TWO, {
        "model-a": ["no", "no",
                    "theorem demo_b : True := by\n  have key : True := by trivial\n  exact key",
                    "have key : True := by trivial", "exact key"],
    }, lines=("model-a",))
    assert {"kind": "route", "by": "model-a", "to": "demo_b"} in result.metadata["events"]
    assert result.metadata["accepted_by_repl"] is True


def test_a_step_that_leaves_the_goal_exactly_as_it_was_is_refused():
    result, lean, llm, _ = run(ONE, {"model-a": ["norm_num", "have key : True := by trivial",
                                                 "exact key"]}, lines=("model-a",))
    first = steps(result)[0]
    assert first["accepted"] is False
    assert any("exactly as it was" in p for _, p in llm.calls)
    assert result.metadata["accepted_by_repl"] is True


def test_a_reply_about_a_goal_the_other_model_already_closed_is_stale():
    result, lean, llm, _ = run(ONE, {
        "model-a": ["have key : True := by trivial", "exact key"],
        "model-b": ["have key : True := by trivial"],
    }, delay={"model-b": 0.5})
    assert result.metadata["accepted_by_repl"] is True
    kinds = [e.get("kind") for e in result.metadata["events"]]
    assert "stale" in kinds or "sorry" not in result.solution


def test_a_rejected_prefix_keeps_the_lines_that_were_right():
    result, lean, llm, _ = run(ONE, {"model-a": ["have key : True := by trivial\nlinarith",
                                                 "exact key"]}, lines=("model-a",))
    assert any(e.get("kind") == "prefix" for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True


def test_restating_a_closed_declaration_pushes_feedback_and_counts():
    # Both goals share a body; a reply that restates the closed sibling must
    # not spin. Measured on p09: a rejection path that touched no counter ran
    # one model 481 times.
    challenge = ("import Mathlib\n\ntheorem demo : True := by\n  sorry\n\n"
                 "theorem demo_b : True := by\n  trivial\n")
    result, lean, llm, _ = run(challenge, {
        "model-a": ["no", "no", "no", "no", "theorem demo_b : True := by trivial",
                    "have key : True := by trivial", "exact key"],
    }, lines=("model-a",))  # the fourth "no" is the second route's skeleton at the crux
    assert [e for e in result.metadata["events"] if e.get("kind") == "drop"]
    assert any("already declared" in p for _, p in llm.calls)


def test_with_one_goal_left_the_fast_model_is_not_idled_by_the_slow_one():
    # Measured on p09: one open goal, held by a model whose reply took 158s,
    # and the other model waited. Both work it; whoever lands first wins.
    result, lean, llm, wall = run(ONE, {
        "model-a": ["have key : True := by trivial", "exact key"],
        "model-b": ["have slow : True := by trivial"],
    }, delay={"model-b": 0.8}, lines=("model-b", "model-a"))
    assert result.metadata["accepted_by_repl"] is True
    # The slow model claimed the only goal first; the fast one finished it
    # anyway. The slow reply, judged against the file it was asked about,
    # becomes a sibling branch; the delivered proof is the finished one.
    events = result.metadata["events"]
    assert any(e.get("stage") == "fork" for e in events) or \
        {"kind": "stale", "by": "model-b"} in events
    assert "have slow" not in result.solution


def test_feedback_names_this_step_s_error_and_not_the_other_open_goals():
    # Measured on p09: with every goal rendered, the first "error" a model was
    # shown for its rejected step was the other worker's open goal.
    result, lean, llm, _ = run(TWO, {
        "model-a": ["no", "linarith", "have key : True := by trivial", "exact key"],
        "model-b": ["no", "have key : True := by trivial", "exact key"],
    })
    told = [p for m, p in llm.calls if m == "model-a" and "rejected" in p]
    assert told, "the rejection was never fed back"
    assert "linarith failed" in told[0]
    assert "⊢ demo_b" not in told[0].split("Lean said")[1]


def test_a_hoisted_lemma_goes_below_the_lemmas_already_there():
    # Measured on p09: a second hoist went above the first and cited it,
    # `Unknown identifier` twice in one run.
    from submission.framework import insert_above
    text = ("import Mathlib\n\ntheorem first_fact : True := by\n  trivial\n\n"
            "/-- doc -/\ntheorem demo : True := by\n  sorry\n")
    out = insert_above(text, "demo", "lemma second : True := by\n  sorry")
    assert out.index("first_fact") < out.index("lemma second") < out.index("/-- doc -/")


def test_a_step_that_empties_a_hypothesis_is_refused():
    # Measured on p09: `simp ... at h ⊢` left `h : True ⊢ False`, no error, and
    # five turns followed on a goal that could not be closed.
    class EmptyingLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source)
            if "simp at h" in source:
                msgs = [dict(m, data=m["data"].replace("⊢ demo", "h : True\n⊢ False"))
                        if "unsolved" in str(m.get("data")) else m for m in check.messages]
                return LeanCheck(check.accepted, msgs, check.has_sorry, False, 1)
            return check
    lean, llm = EmptyingLean(), ScriptLLM({"model-a": ["simp at h", "have key : True := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert steps(result)[0]["accepted"] is False
    assert any("throws the fact away" in p for _, p in llm.calls)
    assert result.metadata["accepted_by_repl"] is True


class ShadowLean(BoardLean):
    """A second `have` of a name already in scope shadows the first, as Lean does."""

    async def check_file(self, source, timeout_s=None):
        check = await super().check_file(source)
        msgs = []
        for m in check.messages:
            d = str(m.get("data", ""))
            if "unsolved" in d:
                names = [l.split(" :")[0] for l in d.split("\n")[1:] if " : " in l]
                for n in set(names):
                    if names.count(n) > 1:
                        d = d.replace(f"{n} : P", f"{n}✝ : P", names.count(n) - 1)
                m = dict(m, data=d)
            msgs.append(m)
        return LeanCheck(check.accepted, msgs, check.has_sorry, False, 1)


def test_a_step_that_only_shadows_an_existing_hypothesis_is_refused():
    # Measured on p10: `have h2 ...` accepted 18 times over, each shadowing the
    # last; the goal text was never the same twice, so nothing called it a stall.
    lean = ShadowLean()
    llm = ScriptLLM({"model-a": ["have key : P := by trivial", "have key : P := by trivial",
                                 "exact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert [e["accepted"] for e in steps(result)][:2] == [True, False]
    assert any("re-declared a name" in p for _, p in llm.calls)
    assert result.solution.count("have key") == 1


def test_a_byte_identical_step_is_not_sent_to_lean_twice():
    result, lean, llm, _ = run(ONE, {"model-a": ["linarith", "linarith", "linarith",
                                                 "have key : P := by trivial", "exact key"]},
                               lines=("model-a",))
    repeats = [e for e in result.metadata["events"] if e.get("kind") == "repeat"]
    assert len(repeats) == 2
    # The one check Lean ran on it, plus the cocktail sweep that names it too.
    assert sum("\n  linarith\n" in s for s in lean.sources) == 1


def test_the_model_sees_every_statement_and_only_its_own_body():
    # Measured on p09: the last 8000 chars of the file cut the shared lemma's
    # statement off the top, and the model cited a lemma it could not see.
    from submission.board.text import view
    from submission.framework import render
    text = ("import Mathlib\n\ntheorem lemma_a (n : ℕ) :\n    n + 0 = n := by\n  simp\n  omega\n\n"
            "theorem lemma_b : True := by\n  sorry\n\n"
            "/-- doc -/\ntheorem demo : True := by\n  have k : True := trivial\n  sorry\n")
    shown, at = view(render(text, 1)[0], "demo")
    assert "n + 0 = n := by\n  -- proved, 2 lines elided" in shown
    assert "simp" not in shown
    assert "theorem lemma_b : True := by\n  sorry" in shown
    assert "have k : True := trivial\n  skip" in shown
    assert shown.split("\n")[at - 1].strip() == "skip"


def test_both_models_shared_facts_are_kept_when_they_differ():
    # Measured on p09: the form of the one shared lemma, chosen by a single
    # call at t=50s, decided 4 of 6 runs. Two true statements cost nothing.
    result, lean, llm, _ = run(TWO, {
        "model-a": ["theorem fact_a : True := by\n  sorry", "have key : P := by trivial", "exact key"],
        "model-b": ["theorem fact_b : True := by\n  sorry", "have key : P := by trivial", "exact key"],
    })
    shares = [e for e in result.metadata["events"] if e.get("stage") == "share"]
    assert [(e["name"], e["kept"]) for e in shares] == [("fact_a", True), ("fact_b", True)]
    first = next(s for s in lean.sources if "theorem demo" in s and "fact_b" in s)
    assert "theorem fact_a" in first and "theorem fact_b" in first


def test_a_goal_object_from_an_older_board_is_found_by_content():
    # Measured on p09 (v5 run): the plan is asked outside the lock, the other
    # worker shifted the file meanwhile, and the old goal object's line was
    # gone; `Board.index` raised ValueError and the problem scored harness_error.
    old = Goal(16, "  ", "demo", "⊢ demo")
    moved = Board(TWO, [Goal(4, "  ", "demo_b", "⊢ demo_b"), Goal(19, "  ", "demo", "⊢ demo")])
    assert moved.index(old) == 1


def test_a_step_that_makes_every_check_slow_is_refused():
    # Measured on p09: one accepted step took the check from 1s to 38s, Lean
    # raised no budget error, and the run lost 5 minutes to the timeout and
    # container restart that followed.
    class SlowLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source)
            ms = 25_000 if "heavy_tactic" in source else 900
            return LeanCheck(check.accepted, check.messages, check.has_sorry, False, ms)
    lean = SlowLean()
    llm = ScriptLLM({"model-a": ["have key : P := by heavy_tactic", "have key : P := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert {"stage": "slow", "ms": 25000, "was": 900} in result.metadata["events"]
    assert "heavy_tactic" not in result.solution and result.metadata["accepted_by_repl"] is True
    # The cap is on the whole file too: a step that adds 4 s to a 24 s file is
    # refused (the judge's cold compile on 4 cores has 180 s; 24 s warm timed out).
    class HeavyLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source)
            ms = 28_000 if "mild_tactic" in source else 24_000
            return LeanCheck(check.accepted, check.messages, check.has_sorry, False, ms)
    lean = HeavyLean()
    llm = ScriptLLM({"model-a": ["have key : P := by mild_tactic", "have key : P := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert {"stage": "slow", "ms": 28000, "was": 24000} in result.metadata["events"]
    assert "mild_tactic" not in result.solution


def test_a_goal_rejected_twice_is_never_probed_for_refutation():
    # Measured on p09 (v7.3): the probe `have refuted : ¬ (target) := by decide
    # | omega` "refuted" six true goals, `⊢ False` under `n % 3 = 1` among them,
    # and undid the proof. Refuting a goal needs a consistent context, which is
    # exactly what a proof by contradiction does not have.
    result, lean, llm, _ = run(ONE, {"model-a": ["linarith", "exact?", "linarith",
                                                 "have key : P := by trivial", "exact key"]},
                               lines=("model-a",))
    assert not any("have refuted" in s for s in lean.sources)
    assert not any(e.get("stage") == "refuted" for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True


def test_the_prefix_cut_is_guided_by_the_first_error_line():
    # Measured: 3.7 Lean checks per model call, most of them prefixes tried
    # longest-first. Lean's first error says where to cut.
    block = "have a : P := by trivial\nhave b : P := by trivial\nlinarith\nhave c : P := by trivial"
    result, lean, llm, _ = run(ONE, {"model-a": [block, "exact a"]}, lines=("model-a",))
    cut = next(e for e in result.metadata["events"] if e.get("kind") == "prefix")
    assert cut["lines"] == 2
    # The failing line is checked once, in the whole block, and never again in
    # a longer-first prefix.
    assert sum("\n  linarith\n" in s for s in lean.sources) == 1
    assert result.metadata["accepted_by_repl"] is True


def test_the_graded_entry_point_can_be_the_board():
    from submission.board_agent import create_agent
    assert isinstance(create_agent(), BoardAgent)


def test_a_reply_cut_by_the_token_limit_keeps_its_complete_steps():
    # Measured on rmo_2001_2: 37 of 70 qwen step calls ended in `length` at
    # 6000 tokens with 13k-24k chars written, and every one was thrown away.
    cut = ("```lean\nhave key : True := by trivial\nhave more : True := by\n"
           "  trivi", "length")
    result, lean, llm, _ = run(ONE, {"model-a": ["no", cut, "exact key"]}, lines=("model-a",))
    assert {"kind": "cut", "by": "model-a", "kept": 1} in result.metadata["events"]
    assert result.metadata["accepted_by_repl"] is True
    assert "have more" not in result.solution


def test_a_step_may_post_a_subgoal_with_sorry():
    # Measured on rmo_2001_2: `have h_gcd : ... := by sorry` was the one
    # decomposition either model offered, and it came back as "no Lean".
    result, lean, llm, _ = run(ONE, {
        "model-a": ["no", "have key : True := by\n  sorry\nexact key", "exact key"],
    }, lines=("model-a",))
    assert [e["accepted"] for e in steps(result)][:1] == [True]
    assert result.metadata["accepted_by_repl"] is True
    assert "sorry" not in result.solution


def test_the_board_tells_the_model_a_sorry_posts_a_subgoal():
    # The cursor loop's system prompt says "give every have a body"; on the
    # board a `have ... := by sorry` is the decomposition it wants.
    result, lean, llm, _ = run(ONE, {"model-a": ["no", "exact key"]}, lines=("model-a",))
    step_systems = [s for s in llm.systems if "competition mathematician" not in s]
    assert step_systems and all("`sorry`" in s and "goal on the board" in s for s in step_systems)
    assert not any("Give every `have` a body" in s for s in step_systems)


def test_after_the_plan_the_next_step_is_asked_as_a_skeleton_of_sorries():
    # Measured on rmo_2001_2: the plan arrived at t=173 and 37 replies then ran
    # past the token cap trying to write it whole. Asked as a skeleton, the plan
    # goes on the board as goals and both workers take them.
    skeleton = "have key : P := by\n  sorry\nhave more : P := by\n  sorry\nexact key"
    result, lean, llm, _ = run(ONE, {
        "model-a": ["linarith", "exact?", "linarith", skeleton, "exact key", "exact key", "exact key"],
    }, lines=("model-a",))
    # two routes at the crux: the second route's skeleton (rejected here) and the main one
    asked = [p for m, p in llm.calls if "Write the plan as a skeleton" in p]
    assert len(asked) == 2 and all("mathematician was asked" in a for a in asked)
    assert {"kind": "skeleton", "by": "model-a"} in result.metadata["events"]
    # Both sorries were posted: a later check rendered two placeholders.
    assert any(src.count("skip") >= 2 for src in lean.sources)
    assert result.metadata["accepted_by_repl"] is True


def test_a_step_that_turns_the_goal_into_false_without_a_new_hypothesis_is_refused():
    # Measured on rmo_2001_2 (v7.6): a wrong witness left `hp : Nat.Prime 3,
    # hq : Nat.Prime 11 ⊢ False`, Lean had no complaint, and 14 turns went into
    # a goal whose context is consistent. `by_contra` adds a hypothesis; a
    # `False` that arrives without one is the step being wrong.
    class FalsifyingLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source)
            if "norm_num [h]" in source:
                msgs = [dict(m, data=m["data"].replace("⊢ demo", "⊢ False"))
                        if "unsolved" in str(m.get("data")) else m for m in check.messages]
                return LeanCheck(check.accepted, msgs, check.has_sorry, False, 1)
            return check
    lean = FalsifyingLean()
    llm = ScriptLLM({"model-a": ["norm_num [h]", "have key : True := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert steps(result)[0]["accepted"] is False
    assert any("into `False`" in p for _, p in llm.calls)
    assert result.metadata["accepted_by_repl"] is True


def test_a_step_that_leaves_a_goal_with_a_metavariable_is_refused():
    # Measured on rmo_2000_2 (v7.8): `apply lt_irrefl _` then `linarith` left
    # `⊢ Type ?u.350` and `⊢ Preorder ?α` open, the board gave each a sorry,
    # both models answered the same line again, six levels deep in 13 minutes.
    class MetaLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source)
            if "apply lt_irrefl _" in source:
                msgs = [dict(m, data=m["data"].replace("⊢ demo", "⊢ Type ?u.350"))
                        if "unsolved" in str(m.get("data")) else m for m in check.messages]
                return LeanCheck(check.accepted, msgs, check.has_sorry, False, 1)
            return check
    lean = MetaLean()
    llm = ScriptLLM({"model-a": ["apply lt_irrefl _", "have key : True := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert steps(result)[0]["accepted"] is False
    assert any("could not infer" in p for _, p in llm.calls)
    assert result.metadata["accepted_by_repl"] is True


def test_a_have_whose_goal_keeps_failing_is_withdrawn_with_everything_after_it():
    # Measured on rmo_2000_2 (v7.8): `have h1 : y^3 > ... := by sorry` posted a
    # false fact at t=64; every goal after it lived in a contradiction and the
    # lemma goal itself could never close. The board has to be able to take a
    # decomposition back.
    # `exact gone` after the have uses its name (the fake reports it unknown once
    # the have is gone), so the whole block goes, as before v7.49.
    result, lean, llm, _ = run(ONE, {
        "model-a": ["have gone : P := by\n  sorry\nexact gone",
                    "linarith", "linarith", "linarith", "linarith",
                    "have other : True := by trivial", "exact other"],
    }, lines=("model-a",))
    events = result.metadata["events"]
    assert any(e.get("kind") == "withdraw" and "gone : P" in e.get("have", "")
               and e.get("whole_block") for e in events)
    assert any("withdrawn" in p for _, p in llm.calls)
    assert "have gone : P" not in result.solution and "exact gone" not in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_a_step_that_times_out_is_not_retried_by_prefix_or_search():
    # Measured on putnam_2018_a1 (v7.10): one divisor enumeration timed the
    # check out at 120s, the container restarted, and the prefix cut then ran
    # the same tactic into the same timeout. Six minutes for one reply.
    class SlowLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            if "decide +kernel" in source:
                self.sources.append(source)
                return LeanCheck(False, [{"severity": "error", "data": "TIMEOUT after 120s"}],
                                 False, True, 120_000)
            return await super().check_file(source)
    lean = SlowLean()
    llm = ScriptLLM({"model-a": ["have big : True := by\n  decide +kernel\nexact big",
                                 "have key : True := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert sum("decide +kernel" in s for s in lean.sources) == 1
    assert any("timed out" in p for _, p in llm.calls)
    assert result.metadata["accepted_by_repl"] is True


def test_a_closer_that_fires_is_flattened_from_its_own_trace_in_one_check():
    # Measured on rmo_2000_2 (v7.8): the closers `first` block closed a goal 9
    # times, and each time `_collapse_last` spent up to 12 more 9.5s checks
    # guessing which alternative had fired, all of them missing. The winner
    # has to announce itself in the check that closes the goal.
    class TracingLean(BoardLean):
        """`omega` closes the goal; every other closer fails. Failed alternatives
        keep their trace (the stricter of Lean's two possible behaviours)."""
        async def check_file(self, source, timeout_s=None):
            self.sources.append(source)
            lines = source.split("\n")
            msgs, closed = [], False
            start = next((i for i, l in enumerate(lines, start=1) if l.startswith("theorem")), 0)
            for i, line in enumerate(lines, start=1):
                body = line.strip()
                if i < start:
                    continue                      # the technique block has its own `first`
                if body == "first":
                    alts = []
                    j = i
                    while j < len(lines) and lines[j].strip().startswith("|"):
                        alts.append((j + 1, lines[j].strip()))
                        j += 1
                    for n, alt in alts:
                        tag = re.search(r'trace "([^"]+)"', alt)
                        if tag:
                            msgs.append({"severity": "info", "pos": {"line": n - 1},
                                         "data": tag.group(1)})
                        if tag and "omega" in alt:
                            closed = True
                            break
                    else:
                        msgs.append({"severity": "error", "pos": {"line": i - 1},
                                     "data": "no closer"})
                elif body in ("skip", PROBE, CELL_PROBE) and closed:
                    closed = False
                    if body in (PROBE, CELL_PROBE):
                        msgs.append({"severity": "error", "pos": {"line": i - 1},
                                     "data": "No goals to be solved"})
                elif body in ("skip", PROBE, CELL_PROBE):
                    msgs.append({"severity": "error", "pos": {"line": i - 2},
                                 "endPos": {"line": i - 1}, "data": "unsolved goals\n⊢ demo"})
                elif body == "omega":
                    closed = True
                elif body in COCKTAIL:
                    msgs.append({"severity": "error", "pos": {"line": i - 1},
                                 "data": f"{body} failed"})
            errors = [m for m in msgs if m["severity"] == "error"]
            return LeanCheck(not errors, msgs, "sorry" in source, False, 1)
    lean = TracingLean()
    llm = ScriptLLM({"model-a": []})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert result.metadata["accepted_by_repl"] is True
    proof = result.solution.split("theorem demo", 1)[1]
    assert "  omega\n" in proof and "first" not in proof
    closed = max(i for i, s in enumerate(lean.sources) if "\n  first\n" in s)
    flat = next(i for i, s in enumerate(lean.sources) if "\n  omega\n" in s)
    assert flat - closed == 1


def test_a_step_is_checked_under_a_timeout_scaled_to_the_base_file():
    # Measured on putnam_2018_a1 (v7.12): the base file checked in 1.3s all
    # run, four steps ran to the harness's 120s timeout, and each timeout also
    # forced a container restart (36..82s). The slow-step guard refuses any
    # step adding over 10s anyway, so the check can be cut far sooner.
    class TimedLean(BoardLean):
        def __init__(self):
            super().__init__()
            self.timeouts: list[tuple[str, int | None]] = []

        async def check_file(self, source, timeout_s=None):
            self.timeouts.append((source, timeout_s))
            check = await super().check_file(source)
            return LeanCheck(check.accepted, check.messages, check.has_sorry,
                             check.timed_out, 1_300)
    lean = TimedLean()
    llm = ScriptLLM({"model-a": ["have key : True := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert result.metadata["accepted_by_repl"] is True
    steps = [t for s, t in lean.timeouts if "have key" in s and "#print axioms" not in s
             and "apply?" not in s]
    assert steps and all(t is not None and t <= 30 for t in steps), steps


def test_the_sweep_does_not_run_exact_search_on_every_goal():
    # Measured over 24 board runs on the pods: the `exact?` sweep closed 1 of
    # 51 goals it was tried on, and under the scaled check timeout a slow
    # `exact?` now also costs a container restart.
    lean = BoardLean()
    llm = ScriptLLM({"model-a": ["have key : True := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert result.metadata["accepted_by_repl"] is True
    assert not any("exact?" in s for s in lean.sources)


class WitnessLean(BoardLean):
    """Real Lean would state each goal and evaluate the witness file; here
    `extract_goal` states the theorem's binders, `intro` names and the enclosing
    `have`'s claim, and any witness file passes."""

    async def check_file(self, source, timeout_s=None):
        if "(w_" in source:
            self.sources.append(source)
            return LeanCheck(True, [], False, False, 1)
        if not any(l.strip().endswith("extract_goal") for l in source.split("\n")):
            return await super().check_file(source, timeout_s)
        lines, messages, binders = source.split("\n"), [], ""
        for i, line in enumerate(lines, start=1):
            head = re.match(r"\s*theorem \w+ (.*) : (.*) := by", line)
            if head:
                binders, target = head.groups()
            if line.strip().startswith("intro "):
                binders += f" ({line.split()[1]} : {target.split('→')[0].strip()})"
            if line.strip().endswith("extract_goal"):
                depth = len(line) - len(line.lstrip())
                above = next((l for l in reversed(lines[:i - 1])
                              if l.strip() and len(l) - len(l.lstrip()) < depth), "")
                prev = lines[i - 2].strip() if i > 1 else ""
                claim = (above.split(":", 1)[1].split(":=")[0].strip()
                         if above.strip().startswith("have") else
                         "False" if prev == "exfalso" else
                         f"P {prev.split()[1]}" if prev.startswith("use ") else
                         target if above.strip().startswith("theorem") else "True")
                messages.append({"severity": "info", "pos": {"line": i - 1},
                                 "data": f"theorem extracted_1 {binders} : {claim} := sorry"})
        return LeanCheck(False, messages, True, False, 1)


def test_a_posted_have_that_a_witness_falsifies_never_reaches_the_board():
    # Measured on putnam_2018_a1 (v7.10, t=833): `have h_divisors : 3a−2018 ∈
    # {...} := by sorry` listed three non-divisors of 2018² and everything after
    # it hung. The other model names values that satisfy every hypothesis and
    # break the claim; Lean checks them in a file of their own.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["have bad : x = 3 := by\n  sorry\nexact key",
                    '{"counterexample": {"x": "0"}}',
                    "have key : True := by trivial\nexact key",
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    witness = [s for s in lean.sources if "(w_" in s]
    assert witness and "(w_x : x = (0))" in witness[0] and "(x < 2) ∧ ¬ (x = 3)" in witness[0]
    assert any(e.get("kind") == "audit" and e.get("verdict") == "refuted"
               for e in result.metadata["events"])
    assert any("x = 0" in p for _, p in llm.calls)
    assert "have bad" not in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_a_model_that_narrates_is_not_the_auditor_while_one_that_answers_is_there():
    # Measured on rmo_2000_2 / putnam_2018_a1 (v7.17–v7.19): qwen as auditor
    # named values that violated a hypothesis in 12 of 12 audits at ~9s each;
    # gpt-oss answered correctly in ~1.4s. The auditor is the model that finds
    # counterexamples, even when it audits its own step.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["have bad : x = 3 := by\n  sorry\nexact key",
                    '{"counterexample": {"x": "0"}}',
                    "have key : True := by trivial\nexact key"],
        "qwen-b": ["have key : True := by trivial\nexact key"] * 3})
    agent = BoardAgent(Config(lines=("model-a", "qwen-b"), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    audits = [k["model"] for k, s in zip(llm.kwargs, llm.systems) if "You audit" in s]
    assert audits and "qwen-b" not in audits
    assert any(e.get("kind") == "audit" and e.get("verdict") == "refuted"
               for e in result.metadata["events"])


def test_a_goal_under_an_intro_is_audited_in_the_context_lean_states():
    # Measured on putnam_2018_a1 (v7.16, one16b): the proof opened with
    # `constructor; intro h_eq`, so every later goal carried a name the header
    # did not bind and 0 of 88 turns were audited; a false `h_bound` went up.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) : x < 2 → True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["intro hx\nhave bad : x = 3 := by\n  sorry\nexact key",
                    '{"counterexample": {"x": "0"}}',
                    "intro hx\nhave key : True := by trivial\nexact key",
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    witness = [s for s in lean.sources if "(w_" in s]
    assert witness and "(x : ℕ) (w_x : x = (0)) : (x < 2) ∧ ¬ (x = 3)" in witness[0]
    assert any(e.get("kind") == "audit" and e.get("verdict") == "refuted"
               for e in result.metadata["events"])
    assert "have bad" not in result.solution


def test_a_fact_posted_inside_a_have_lands_above_the_outermost_have():
    # Measured on rmo_2000_2 (v7.19): every goal two rejections deep got a
    # skeleton at its own depth, so `have`s nested seven levels, 25 goals were
    # open at once and the withdraw count restarted with each layer.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    result, lean, llm, _ = run(challenge, {
        "model-a": ["have outer : True := by\n  sorry\nexact outer",
                    "have inner : 1 = 1 := by\n  sorry\nhave key : True := by trivial\nexact key",
                    "have key2 : True := by trivial\nexact key2"]}, lines=("model-a",))
    text = result.solution
    assert "have inner" in text and text.index("have inner") < text.index("have outer")
    assert any(e.get("kind") == "lifted" and e.get("from_depth") == 1
               for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True


def test_a_fact_already_on_the_board_is_not_posted_twice():
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    result, lean, llm, _ = run(challenge, {
        "model-a": ["have outer : True := by\n  sorry\nexact outer",
                    "have again : True := by\n  sorry\nhave key : True := by trivial\nexact key"]},
        lines=("model-a",))
    assert "have again" not in result.solution
    assert any(e.get("kind") == "lifted" and e.get("dup") == 1
               for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True


def test_only_a_goal_the_model_stated_is_audited():
    # Measured (v7.21, first 10 min of rmo_2000_2): 30 audits in 95 calls, 48%
    # of the wall clock under the lock; every false statement ever caught was a
    # `have`. A goal Lean derived from a tactic is not sent to the auditor.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["constructor\n· sorry\n· sorry",
                    "have key : True := by trivial\nexact key",
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    assert not any("You audit" in s for s in llm.systems)
    assert not any(e.get("kind") == "audit" for e in result.metadata["events"])


class AnswerLean(WitnessLean):
    """A witness file passes only at the one pair that breaks the theorem."""

    async def check_file(self, source, timeout_s=None):
        if "(w_" in source:
            self.sources.append(source)
            return LeanCheck("(w_a : a = (0)) (w_b : b = (3))" in source, [], False, False, 1)
        return await super().check_file(source, timeout_s)


def test_an_answer_term_a_witness_breaks_is_not_used():
    # Measured on putnam_2018_a1 (v7.22, one22b): the first elaborating answer
    # was a set-builder with integer division, the `↔` was false from t=0 and
    # 45 minutes went into an unprovable theorem. Each offer is tried against
    # the theorem's own statement; an element that breaks it sinks the offer.
    challenge = ("import Mathlib\n\nabbrev demo_solution : Set (ℕ × ℕ) := by\n  sorry\n\n"
                 "theorem demo (a b : ℕ) : a + b = 2 ↔ (a, b) ∈ demo_solution := by\n  sorry\n")
    lean, llm = AnswerLean(), ScriptLLM({
        "model-a": ["({(1, 1), (0, 3)} : Set (ℕ × ℕ))", '{"holds": true}',
                    "have key : True := by trivial\nexact key"] * 2,
        "model-b": ["({(1, 1), (2, 0), (0, 2)} : Set (ℕ × ℕ))",
                    "have key : True := by trivial\nexact key"] * 2})
    agent = BoardAgent(Config(lines=("model-a", "model-b"), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    defines = [e for e in result.metadata["events"] if e.get("stage") == "define"]
    assert [d["verdict"] for d in defines] == ["refuted", "holds"]
    assert defines[0]["values"] == {"a": "0", "b": "3"}
    assert "(2, 0)" in result.solution and "(0, 3)" not in result.solution


def test_a_model_that_narrates_is_asked_for_the_answer_term_with_reasoning_off():
    challenge = ("import Mathlib\n\nabbrev demo_solution : Set (ℕ × ℕ) := by\n  sorry\n\n"
                 "theorem demo (a b : ℕ) : a + b = 2 ↔ (a, b) ∈ demo_solution := by\n  sorry\n")
    lean, llm = AnswerLean(), ScriptLLM({
        "model-a": ["({(1, 1), (2, 0), (0, 2)} : Set (ℕ × ℕ))", '{"holds": true}',
                    "have key : True := by trivial\nexact key"] * 2,
        "qwen-b": ["({(1, 1), (2, 0), (0, 2)} : Set (ℕ × ℕ))",
                   "have key : True := by trivial\nexact key"] * 2})
    agent = BoardAgent(Config(lines=("model-a", "qwen-b"), budget_usd=1.0, time_limit_s=600.0))
    asyncio.run(agent.solve(Problem(id="demo", description="prove it", challenge=challenge),
                            FakeServices(lean, llm)))
    asked = [k for k, p in zip(llm.kwargs, [p for _, p in llm.calls])
             if k["model"] == "qwen-b" and "Give the value of" in p]
    assert asked and all(k["reasoning"] == {"enabled": False} for k in asked)


def test_a_hoisted_lemma_a_witness_breaks_does_not_enter_the_file():
    # Measured on putnam_2020_a2 (v7.23): `binomial_split` was hoisted with a
    # statement false at j = 0 (ℕ subtraction) and the proof built on it.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["theorem bad (x : ℕ) : x = 3 := by\n  sorry",
                    '{"counterexample": {"x": "0"}}',
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    assert "theorem bad" not in result.solution
    assert any(e.get("kind") == "lemma" and e.get("accepted") is False
               for e in result.metadata["events"])
    assert any(e.get("kind") == "audit" and e.get("verdict") == "refuted"
               for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True


def test_a_model_that_narrates_is_asked_for_the_shared_lemma_with_reasoning_off():
    # Measured on p09 (gate22, 6 of 6 runs): qwen's shared-lemma reply was
    # prose, `kept: False, name: ''`; the run that got only `2^3 % 7 = 1` from
    # the other model failed where the cycle lemma runs succeeded.
    lean, llm = BoardLean(), ScriptLLM({
        "model-a": ["no", "have key : True := by trivial", "exact key"],
        "qwen-b": ["no", "have key : True := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a", "qwen-b"), budget_usd=1.0, time_limit_s=600.0))
    asyncio.run(agent.solve(Problem(id="demo", description="prove it", challenge=TWO),
                            FakeServices(lean, llm)))
    share = [k for k, (m, p) in zip(llm.kwargs, llm.calls)
             if m == "qwen-b" and "graded together" in p]
    assert share and all(k["reasoning"] == {"enabled": False} for k in share)


def test_a_have_with_a_proof_body_has_its_claim_audited_too():
    # Measured on putnam_2020_a2 (v7.25): `have h3 : ∀ x ∈ Icc 0 k, …` was false
    # at k = 1 but came with a proof body, so only the body's residue was
    # audited and the false claim went up on the board.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["have bad : x = 3 := by\n  omega\nhave key : True := by trivial\nexact key",
                    '{"counterexample": {"x": "0"}}',
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    assert "have bad" not in result.solution
    assert any(e.get("kind") == "audit" and e.get("verdict") == "refuted"
               and e.get("goal") == "x = 3" for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True


def test_a_withdrawn_claim_blocks_only_a_have_that_states_it_again():
    # Measured on p09 (gate26 run 4): after `have h_case : n % 3 = 0` was
    # withdrawn, every step containing the text `n % 3 = 0` was refused before
    # Lean saw it, and the goal itself was `⊢ n % 3 = 0`: 330 refusals in 19 min.
    from submission.board.text import restates
    assert restates("have h2 : n % 3 = 0 := by\n  omega", ["n % 3 = 0"])
    assert restates("have h2 :  n % 3 = 0  := by omega", ["n % 3 = 0"])
    assert not restates("rcases h with h | h\nomega", ["n % 3 = 0"])
    assert not restates("have h2 : 2 ^ (n % 3) % 7 = 1 → n % 3 = 0 := by\n  omega", ["n % 3 = 0"])
    assert not restates("exact (by omega : n % 3 = 0)", ["n % 3 = 0"])


def test_the_slow_model_is_asked_for_steps_under_the_read_timeout_budget():
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    result, lean, llm, _ = run(challenge, {
        "model-a": ["have key : True := by trivial\nexact key"],
        "qwen-b": ["have key : True := by trivial\nexact key"]}, lines=("model-a", "qwen-b"))
    steps = [k for k, s in zip(llm.kwargs, llm.systems) if "goal on the board" in s]
    assert {k["max_tokens"] for k in steps if k["model"] == "model-a"} <= {4000}
    assert {k["max_tokens"] for k in steps if k["model"] == "qwen-b"} <= {6000}
    assert steps


def test_a_goal_a_model_repeats_itself_on_goes_to_the_end_of_its_line():
    # Measured on putnam_2020_a2 (v7.27): 274 step calls in 23 min, the same
    # rejected step to the same goal every 2 s. After a repeat the goal is the
    # last one that model picks, so it moves to the other open goal and the
    # other model gets the repeated one.
    challenge = ("import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n\n"
                 "theorem demo_b (x : ℕ) (hx : x < 2) : True := by\n  sorry\n")
    lean, llm = BoardLean(), ScriptLLM({
        "model-a": ["no", "first\n  | linarith", "first\n  | linarith", "first\n  | linarith"]
                   + ["have key : True := by trivial\nexact key"] * 3,
        "model-b": ["no"] + ["have key : True := by trivial\nexact key"] * 3},
        delay={"model-b": 1.5})
    agent = BoardAgent(Config(lines=("model-a", "model-b"), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    assert "repeat" in [e.get("kind") for e in result.metadata["events"]]
    prompts = [p for (m, p), sys_ in zip(llm.calls, llm.systems)
               if m == "model-a" and "goal on the board" in sys_]
    goals = [p.split("⊢ ", 1)[1].split("\n", 1)[0] if "⊢ " in p else "" for p in prompts]
    # the second `demo` prompt is the repeat; the next pick is the other goal
    assert goals[:3] == ["demo", "demo", "demo_b"]
    assert result.metadata["accepted_by_repl"] is True


def test_a_statement_split_over_lines_is_still_audited():
    # Measured on putnam_2018_a1 (v7.23): `have h_cases :` followed by six
    # indented disjuncts and `:= by` on the last line matched no reader of the
    # board, so it was neither audited nor lifted nor withdrawable.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["have bad :\n    x = 3 ∨\n    x = 4 := by\n  sorry\nexact key",
                    '{"counterexample": {"x": "0"}}',
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    assert any(e.get("kind") == "audit" and e.get("verdict") == "refuted"
               and e.get("goal") == "x = 3 ∨ x = 4" for e in result.metadata["events"])
    assert "have bad" not in result.solution


def test_a_graded_theorems_residual_goal_is_not_audited_as_a_statement():
    # A step leaves the theorem's own goal open after it; that goal is Lean's,
    # not a statement the model wrote, and auditing it at every step doubled
    # the audit calls (v7.25 counted any goal under a `theorem` head).
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["have h1 : x < 5 := by\n  omega", '{"holds": true}',
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    audits = [e for e in result.metadata["events"] if e.get("kind") == "audit"]
    assert [a["goal"] for a in audits] == ["x < 5"]
    assert result.metadata["accepted_by_repl"] is True


class DeadEndLean(WitnessLean):
    """Only the witness against `False` passes: the context is satisfiable."""

    async def check_file(self, source, timeout_s=None):
        if "(w_" in source:
            self.sources.append(source)
            return LeanCheck("¬ (False)" in source, [], False, False, 1)
        return await super().check_file(source, timeout_s)


def test_a_false_goal_in_a_satisfiable_context_is_refused():
    # Measured on p09 (gate32 run 1): a wrong case split left `h : n % 3 = 1`,
    # `h_mod : 2 ^ n % 7 = 2`, `¬7 ∣ 2 ^ n - 1 ⊢ False`, satisfiable at n = 1;
    # both models spent the rest of the run trying to prove it.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = DeadEndLean(), ScriptLLM({
        "model-a": ["have h1 : x < 1 := by\n  omega\nexfalso\nsorry",
                    '{"counterexample": {"x": "0"}}', '{"counterexample": {"x": "0"}}',
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    assert any(e.get("kind") == "audit" and e.get("verdict") == "refuted"
               and e.get("goal") == "False" for e in result.metadata["events"])
    assert "exfalso" not in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_a_fact_already_proved_in_scope_is_not_proved_again():
    # Measured on p09 (gate33 run 1): the same claim proved twice in one
    # declaration, one `have` inside the other, and both models working on both.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    result, lean, llm, _ = run(challenge, {
        "model-a": ["have h1 : x < 5 := by\n  omega\nhave key : True := by trivial\nexact key"]
                   * 1 + ["have h1' : x < 5 := by\n  omega\nexact key"],
        "model-b": ["have h1 : x < 5 := by\n  omega",
                    "have again : x < 5 := by\n  omega\nhave key : True := by trivial\nexact key",
                    "have key : True := by trivial\nexact key"]},
        lines=("model-b",))
    assert any(e.get("kind") == "restated" and e.get("of") == ["h1"]
               for e in result.metadata["events"])
    assert "have again" not in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_the_same_shared_lemma_under_two_names_is_kept_once():
    # Measured on p09 (gate33 run 1): both models proposed `2 ^ n % 7 = 2 ^ (n % 3) % 7`
    # under different names, and the board proved both.
    from submission.board.text import drop_declaration
    from submission.board.types import signature
    text = ("import Mathlib\ntheorem a_cycle (n : ℕ) : 2 ^ n % 7 = 2 ^ (n % 3) % 7 := by\n  sorry\n\n"
            "theorem b_cycle (n : ℕ) :  2 ^ n % 7 = 2 ^ (n % 3) % 7 := by\n  sorry\n\n"
            "theorem other (n : ℕ) : 2 ^ n % 7 < 7 := by\n  sorry\n")
    assert signature(text, "a_cycle") == signature(text, "b_cycle")
    assert signature(text, "a_cycle") != signature(text, "other")
    dropped = drop_declaration(text, "b_cycle")
    assert "b_cycle" not in dropped and "a_cycle" in dropped and "other" in dropped


def test_a_rewrite_that_unfolds_a_variable_everywhere_is_measured_as_inflation():
    # Measured on rmo_2001_2 (v7.32), p09 (gate29 run 1, gate26 run 4) and
    # rmo_2000_2: `rw [← Nat.mod_add_div p 9] at *` turned every `p` in every
    # hypothesis into `p % 9 + 9 * (p / 9)` and the run never recovered.
    from submission.board.text import inflated
    before = ("p q : ℕ\nhp : Nat.Prime p\nhq : Nat.Prime q\nm : ℕ\n"
              "hm : p ^ 2 + 7 * p * q + q ^ 2 = m ^ 2\n⊢ p = q ∨ p = 3 ∧ q = 11")
    after = ("p q : ℕ\nhp : Nat.Prime (p % 9 + 9 * (p / 9))\nhq : Nat.Prime (q % 9 + 9 * (q / 9))\nm : ℕ\n"
             "hm : (p % 9 + 9 * (p / 9)) ^ 2 + 7 * (p % 9 + 9 * (p / 9)) * (q % 9 + 9 * (q / 9)) "
             "+ (q % 9 + 9 * (q / 9)) ^ 2 = m ^ 2\n⊢ p = q")
    assert inflated(before, after) >= 3.0
    # a skeleton adds hypotheses and a field_simp reshapes one: neither counts as inflation
    skeleton = before.replace("⊢", "h1 : 3 ∣ p + q\nh2 : m % 3 = 0\nh3 : p < q\nh4 : q < m\n⊢")
    assert inflated(before, skeleton) == 1.0
    reshaped = before.replace("hm : p ^ 2 + 7 * p * q + q ^ 2 = m ^ 2",
                              "hm : p * p + 7 * (p * q) + q * q = m * m ∧ 0 < m")
    assert inflated(before, reshaped) < 2.0
    # unfolding an answer set in one hypothesis is growth without repetition
    mem = "a b : ℤ\nh : 0 < a ∧ 0 < b\nh_in : (a, b) ∈ putnam_2018_a1_solution\n⊢ True"
    unfolded = mem.replace("putnam_2018_a1_solution", "{(673, 1358114), (674, 340033), "
                           "(1009, 2018), (2018, 1009), (340033, 674), (1358114, 673)}")
    assert inflated(mem, unfolded) == 1.0


def test_a_big_operator_written_with_in_is_spelled_the_way_this_mathlib_reads_it():
    # Measured on rmo_2000_3 (65 rejections, 208 occurrences) and putnam_2020_a2
    # (14 rejections): both models write `∑ j in Finset.Icc 0 k`, the spelling
    # Mathlib replaced by `∑ j ∈ s`, and Lean's "unexpected token 'in'" never
    # tells them so. The rename is lexical; the term means the same.
    from submission.board.reply import dialect
    assert dialect("have h : ∑ j in Finset.Icc 0 k, f j = ∏ (i : ℕ) in s, g i := by\n"
                   "  simp") == ("have h : ∑ j ∈ Finset.Icc 0 k, f j = ∏ (i : ℕ) ∈ s, g i := by\n"
                                 "  simp")
    # `in` anywhere else is left alone
    kept = "set_option maxHeartbeats 400000 in\nsimp only [Finset.sum_range_succ] at h ⊢"
    assert dialect(kept) == kept
    assert dialect("∑ x ∈ s, x") == "∑ x ∈ s, x"
    # and interpret() applies it once, so every edit (step or hoisted lemma)
    # carries the new spelling. Measured one37a: a hoisted lemma kept `in`.
    goal = Goal(2, "  ", "t", "⊢ True")
    board = Board("theorem t : True := by\n  sorry", [goal])
    edits = interpret("```lean\nhave h : ∑ j in Finset.range 3, j = 3 := by sorry\n"
                      "lemma l (k : ℕ) : ∑ j in Finset.range k, j = k := by\n  sorry\n```",
                      board, goal, ["t"])
    assert [e.kind for e in edits] == ["step", "hoist"]
    assert all(" in " not in e.block + e.body and "∈" in e.block + e.body for e in edits)


def test_a_proved_fact_re_derived_inside_a_new_claims_body_is_not_a_restatement():
    # Measured on rmo_2000_6 (one35a): `have h_v5 : 5 ∣ a * b := by\n  have : 5 ∣ a ^ 2
    # * b ^ 5 := h5_pow ...` was refused twice as "already on the board as h5";
    # the new claim was new, only a local alias inside its body repeated h5.
    from submission.board.text import restates
    block = ("have h_v5 : 5 ∣ a * b := by\n"
             "  have : (5 : ℕ) ∣ a ^ 2 * b ^ 5 := h5_pow\n"
             "  exact Nat.Prime.dvd_of_dvd_pow Nat.prime_five this")
    assert not restates(block, ["(5 : ℕ) ∣ a ^ 2 * b ^ 5"])
    assert restates(block, ["5 ∣ a * b"])
    assert restates("  have : (5 : ℕ) ∣ a ^ 2 * b ^ 5 := h5_pow", ["(5 : ℕ) ∣ a ^ 2 * b ^ 5"])


def test_a_board_with_every_goal_last_in_line_starts_the_declaration_over():
    # Measured across 43 archived runs: the restart never fired once, because it
    # was reachable only when no goal could be picked, and a goal can always be
    # picked. A stuck board ground on unchanged until the clock ran out.
    challenge = "import Mathlib\n\ntheorem demo (n : ℕ) : True := by\n  sorry\n"
    result, lean, llm, _ = run(challenge, {
        "model-b": ["induction n with\n| zero => sorry\n| succ k ih => sorry"]
                   + [f"linarith [h{i}]" for i in range(1, 15)]
                   + ["have key : True := by trivial\nexact key"] * 2},
        lines=("model-b",), time_limit=60)
    assert any(e.get("stage") == "restate" for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True
    assert "induction" not in result.solution


def test_a_lean_3_comma_at_the_end_of_a_tactic_line_is_dropped():
    # Measured on r3's archive: 38 of 868 step replies had a tactic line ending
    # in a comma, every one rejected with "expected command", and qwen wrote
    # the next one the same way after being told (rmo_2000_6 one40a, twice).
    from submission.board.reply import dialect
    assert dialect("intro n hn,\nsimp [p10_answer] at hn ⊢,\nexact h") == \
        "intro n hn\nsimp [p10_answer] at hn ⊢\nexact h"
    # a comma that continues a list on the next line, or sits inside an open
    # bracket, is not a Lean 3 comma
    assert dialect("use 1,\n  2") == "use 1,\n  2"
    assert dialect("refine ⟨a,\n  b⟩") == "refine ⟨a,\n  b⟩"
    assert dialect("simp only [foo,\n  bar] at h") == "simp only [foo,\n  bar] at h"
    assert dialect("· norm_num [Nat.factorial],") == "· norm_num [Nat.factorial]"


def test_a_misspelt_library_name_comes_back_with_the_nearest_real_ones():
    # Measured on r3's archive: 99 of 610 rejections named an unknown identifier;
    # after the locals, the top ones were renamed Mathlib lemmas (div_le_div_iff 19,
    # Int.mod_eq_of_lt 12, Finset.Ico.mem 12). Lean's environment knows the real names.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) : True := by\n  sorry\n"
    result, lean, llm, _ = run(challenge, {
        "model-b": ["exact Nat.mod_pow_self x", "exact Nat.mod_pow_self x",
                    "have key : True := by trivial\nexact key"]},
        lines=("model-b",))
    prompts = [p for m, p in llm.calls if "Nearest that exist" in p]
    assert prompts and "Nat.real_mod_pow_self" in prompts[0]
    asked = [e for e in result.metadata["events"] if e.get("stage") == "names"]
    assert len(asked) == 1 and asked[0]["asked"] == ["Nat.mod_pow_self"]
    # the local `x` and hypothesis-style names never go to Lean
    from submission.board.probes import library_names
    assert library_names([{"data": "Unknown identifier `x`"}, {"data": "Unknown identifier `h_k`"},
                          {"data": "Unknown identifier `k.succ`"}], "k x : ℕ\n⊢ True") == []
    # a field access that does not resolve names the constant Lean looked for
    assert library_names([{"data": "Invalid field `dvd_pow`: The environment does not contain "
                                   "`Irreducible.dvd_pow`, so it is not possible"}], "⊢ True") \
        == ["Irreducible.dvd_pow"]


def test_the_crux_opens_two_routes_and_the_second_can_be_the_one_that_closes():
    # Measured on rmo_2000_6, putnam_2018_a1 and rmo_2001_2: one plan per crux,
    # and every run deepened the first route it was given. Two plans, one per
    # model, the second written onto a sibling branch; Lean decides between them.
    # Queue: two rejected steps, then at the crux the second route's skeleton
    # (closes), then the main route's skeleton (a dead end).
    result, lean, llm, _ = run(ONE, {
        "model-a": ["no", "linarith [a]",
                    "have key : True := by trivial\nexact key",
                    "have dead : P := by\n  sorry\nexact dead"],
    }, lines=("model-a",))
    planners = [p for m, p in llm.calls if p.startswith("Problem: prove it\n\nThe goal")]
    assert len(planners) == 2
    assert any(e.get("stage") == "route" for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True
    assert "dead" not in result.solution


def test_after_a_restart_the_next_plan_is_asked_to_avoid_the_routes_already_tried():
    # Measured on rmo_2001_2: after the board was cut back the models proposed
    # the same decomposition again. Plans are remembered per declaration across
    # restarts and the planner is told which ones to avoid.
    challenge = "import Mathlib\n\ntheorem demo (n : ℕ) : True := by\n  sorry\n"
    result, lean, llm, _ = run(challenge, {
        "model-b": ["no", "linarith [h1]", "linarith [h2]"]
                   + ["linarith [h%d]" % i for i in range(3, 22)]
                   + ["have key : True := by trivial\nexact key"] * 3},
        lines=("model-b",), time_limit=60)
    planners = [p for m, p in llm.calls if p.startswith("Problem: prove it\n\nThe goal")]
    assert len(planners) >= 4
    assert "Routes already tried" not in planners[0]
    assert "Routes already tried" in planners[-1] and "Take the obvious route (" in planners[-1]


def test_a_filler_fact_does_not_rank_a_branch_ahead():
    # v7.44 ranked branches by proved `have`s first; under the fake, the branch
    # that collected `have junk : True := by trivial` on every idle turn outranked
    # the one making progress, and models post fillers too (`h_a_ge_1`, `h_a_ge_2`
    # both `a ≥ 1` on rmo_2000_6). Open goals, then age.
    filler = ("theorem t : True := by\n  have junk : True := by\n    trivial\n"
              "  have junk2 : True := by\n    trivial\n  sorry\n  sorry\n")
    lean = "theorem t : True := by\n  sorry\n"
    f = Board(filler, [Goal(6, "  ", "t", "⊢ True"), Goal(7, "  ", "t", "⊢ True")])
    l = Board(lean, [Goal(2, "  ", "t", "⊢ True")])
    assert sorted([f, l], key=lambda b: b.score)[0] is l


def test_a_fact_about_a_variable_bound_inside_the_have_stays_inside_it():
    # Measured on rmo_2000_6 (one44a): the crux sat inside `have h_minimal : ∀ n,
    # ... := by intro n h; rcases h with ⟨a, b, ...⟩`, and every fact about a
    # and b was lifted above it, where a and b do not exist: "Unknown identifier
    # a", step refused. Lean says where the fact can live; lifting stops there.
    result, lean, llm, _ = run(ONE, {
        "model-a": ["have outer : True := by\n  intro loc\n  sorry\nexact outer",
                    "have inner : uses loc := by\n  sorry\nexact inner",
                    "exact outer", "exact outer"],
    }, lines=("model-a",))
    assert "have inner" in result.solution
    assert result.solution.index("intro loc") < result.solution.index("have inner")
    assert result.metadata["accepted_by_repl"] is True


def test_a_claim_that_enters_through_a_prefix_cut_is_audited_too():
    # Measured on rmo_2000_6 (one45a, 05:43:58): a skeleton whose whole block was
    # rejected came in as its accepted prefix, unaudited, carrying `h1 : 2000 ∣
    # 4 ^ 2 * 1 ^ 5` (false); the closers then proved three goals from it.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["have bad : x = 3 := by\n  sorry\nlinarith",
                    '{"counterexample": {"x": "0"}}',
                    "have key : True := by trivial\nexact key",
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    assert any(e.get("kind") == "audit" and e.get("verdict") == "refuted"
               for e in result.metadata["events"])
    assert "have bad" not in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_with_two_routes_open_the_second_worker_takes_the_other_one():
    # Measured on rmo_2000_6 (one46a): both workers went to the better-ranked
    # route and the other got 2 turns in 40. A branch the other model is on
    # comes after the ones it is not, so two workers cover two routes.
    # model-a: two rejections, then the crux; its two skeletons each leave one
    # goal open. model-b arrives after the crux and can only close the fork's
    # goal (k1); on the main branch its step does nothing.
    result, lean, llm, _ = run(ONE, {
        "model-a": ["no", "linarith [a]",
                    "have k1 : P := by\n  sorry\nhave k2 : Q := by\n  sorry\n"
                    "have k3 : R := by\n  sorry\nexact k1",                      # second route
                    "have gone : P := by\n  sorry\nhave gone2 : Q := by\n  sorry\nexact gone"]
                   + [f"linarith [x{i}]" for i in range(400)],
        "model-b": ["exact k1"] * 6,      # three go to the skeleton's audits
    }, delay={"model-a": 0.05, "model-b": 0.6}, time_limit=60)
    assert any(e.get("stage") == "route" for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True
    assert "k1" in result.solution and "gone" not in result.solution
    assert not re.search(r":= by\n\s*(?:have|exact|$)", result.solution.split("k1 : P", 1)[1]
                         .split("theorem", 1)[0].replace(":= by\n    exact", ""))


class ClosedLean(WitnessLean):
    """The witness against `P 10` passes (10 is the wrong witness); `P 5` holds."""

    async def check_file(self, source, timeout_s=None):
        if "(w_" in source or "¬ (P " in source:
            self.sources.append(source)
            return LeanCheck("¬ (P 10)" in source, [], False, False, 1)
        return await super().check_file(source, timeout_s)


def test_a_step_that_leaves_a_closed_false_goal_is_refused_without_a_model_call():
    # Measured on rmo_2000_6 (one46a 06:03): `use 10; use 1` left `⊢ 0 < 1 ∧
    # 2000 ∣ 10 ^ 3 * 1 ^ 4 ∧ 10 = 10 * 1`, false and variable-free; Lean took the
    # step and the branch was dead until withdrawal. A new goal with nothing in
    # scope is tried against its own negation, no auditor needed.
    challenge = "import Mathlib\n\ntheorem demo : True := by\n  sorry\n"
    lean, llm = ClosedLean(), ScriptLLM({
        "model-a": ["use 10\nsorry", "use 5\nsorry", "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    audits = [e for e in result.metadata["events"] if e.get("kind") == "audit"]
    assert any(e.get("verdict") == "refuted" and e.get("goal") == "P 10" for e in audits)
    assert not any("Is the target a consequence" in p for _, p in llm.calls)
    assert "use 10" not in result.solution and "use 5" in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_withdrawing_a_fact_keeps_the_independent_facts_after_it():
    # Measured on rmo_2000_6 (one48a 06:37): `h_witness` was withdrawn after 4
    # failed attempts and took `h_min`, the whole crux, down with it, though
    # h_min never used it. Only the have goes; Lean says whether anything after
    # it depended on it, and only then does the rest of the block go too.
    result, lean, llm, _ = run(ONE, {
        "model-a": ["have bad : P := by\n  sorry\nhave good : Q := by\n  sorry\nexact good"]
                   + [f"linarith [x{i}]" for i in range(7)] + ["exact good", "exact good"],
    }, lines=("model-a",))
    assert any(e.get("kind") == "withdraw" and "bad" in e.get("have", "")
               for e in result.metadata["events"])
    assert "have good" in result.solution and "have bad" not in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_a_reply_that_rewrites_the_enclosing_case_and_have_is_unwrapped():
    # Measured on rmo_2000_6 (one49a, 3 times at the membership step): asked for
    # the body of `have h₁ : ... := by` under `case left =>`, qwen answered
    # `case left =>\n  have h₁ : ... := by\n    refine ⟨1, 10, ...⟩`, and Lean
    # said "Case tag `left` not found". The context it copied is stripped.
    from submission.board.reply import unwrap
    text = ("theorem t : True := by\n  constructor\n  case left =>\n"
            "    have h₁ : ∃ a b : ℕ, 10 = a * b := by\n      sorry\n    exact h₁\n"
            "  case right =>\n    sorry\n")
    goal = Goal(5, "      ", "t", "⊢ ∃ a b, 10 = a * b")
    wrapped = ("case left =>\n  have h₁ : ∃ a b : ℕ, 10 = a * b := by\n"
               "    refine ⟨1, 10, ?_⟩\n    norm_num")
    assert unwrap(wrapped, text, goal) == "refine ⟨1, 10, ?_⟩\nnorm_num"
    # only the enclosing context is stripped; a fresh have or another case is a step
    assert unwrap("have h₂ : True := by\n  trivial", text, goal) == "have h₂ : True := by\n  trivial"
    assert unwrap("case right =>\n  trivial", text, goal) == "case right =>\n  trivial"


def test_a_hoisted_lemma_whose_goal_keeps_failing_is_dropped_like_a_have():
    # Measured on rmo_2000_6 (one49a 06:57): a model hoisted `rmo_2000_6_part1 :
    # IsLeast S 20` (false; the original contest answer), the audit could not
    # decide a closed IsLeast, and nothing ever took the lemma back: a `have`
    # is withdrawn after WITHDRAW_AFTER failures, a lemma was not.
    result, lean, llm, _ = run(ONE, {
        "model-a": ["lemma part1 : P := by\n  sorry", "linarith [x0]",
                    "have key : True := by trivial\nexact key"]
                   + [f"linarith [x{i}]" for i in range(1, 9)],
    }, lines=("model-a",))
    events = result.metadata["events"]
    # Taken back by the withdrawal, or shed at the finish as an open helper nothing uses (v7.97).
    assert any((e.get("kind") == "withdraw" and e.get("decl") == "part1")
               or (e.get("stage") == "shed" and e.get("name") == "part1") for e in events)
    assert "lemma part1" not in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_a_closed_goal_is_one_whose_target_names_no_hypothesis():
    # Measured on rmo_2000_6 (one51a 07:13): `use 2; use 5` left `⊢ 0 < 5 ∧ 2000 ∣
    # 8 * 5 ^ 4 ∧ 10 = 2 * 5` (false) under `h_a : 0 < 5`, `h_div : ...`; with
    # "no hypotheses" as the test it was not audited and the branch died.
    from submission.board.probes import is_closed
    assert is_closed("h_a : 0 < 5\nh_div : 2000 ∣ 5 ^ 3 * 2 ^ 4\n⊢ 0 < 5 ∧ 2000 ∣ 8 * 5 ^ 4 ∧ 10 = 2 * 5")
    assert is_closed("⊢ 2000 ∣ 4 ^ 2 * 1 ^ 5")
    assert not is_closed("a b : ℕ\nha : 0 < a\n⊢ 10 ≤ a * b")
    assert not is_closed("⊢ ∃ a b, 0 < a ∧ 10 = a * b")
    assert not is_closed("⊢ True") and not is_closed("⊢ demo")  # nothing to evaluate


def test_a_goal_keeps_its_history_when_a_fact_is_added_above_it():
    # Measured on rmo_2000_6 (one52b): every lifted fact changed the hypothesis
    # list, hence the key, of every goal below it; tries reset, and with all
    # goals at 0 the line order decided: `case inl` got 2 prompts in 28 minutes.
    from submission.board.types import Notes, inherit
    old = [Goal(5, "  ", "t", "a : ℕ\n⊢ P a"), Goal(9, "  ", "t", "a : ℕ\n⊢ Q a")]
    new = [Goal(5, "  ", "t", "a : ℕ\n⊢ R a"),            # the fact just posted
           Goal(7, "  ", "t", "a : ℕ\nx : R a\n⊢ P a"),   # the same goals, one hypothesis richer
           Goal(11, "  ", "t", "a : ℕ\nx : R a\n⊢ Q a")]
    notes = Notes()
    notes[old[0].key].tries, notes[old[1].key].tries = 3, 1
    notes[old[1].key].said = "feedback"
    inherit(old, new, notes)
    assert notes[new[1].key].tries == 3 and notes[new[2].key].tries == 1
    assert notes[new[2].key].said == "feedback"
    assert notes[new[0].key].tries == 0        # the fact just posted starts clean
    # two candidates with the same target: no guess
    twin = new + [Goal(13, "  ", "t", "a : ℕ\nx : R a\n⊢ Q a")]
    fresh = Notes()
    fresh[old[1].key].tries = 1
    inherit(old, twin, fresh)
    assert fresh[new[2].key].tries == 0


def test_an_existential_goal_with_a_decidable_body_gets_its_witness_from_evaluation():
    # Measured on rmo_2000_6 (one52c, 12 min in): both models guessed witnesses
    # for `10 ∈ {n | ∃ a b, … ∧ n = a * b}` (`use 10, 1`, `use 2, 4`) and each
    # wrong guess cost a model call and an audit; the only small witness is
    # a = 1, b = 10. Lean finds it by evaluating the body over 0..39 in one check.
    from submission.board.probes import existential, read_witnesses, witness_search_file
    member = "⊢ 10 ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b}"
    assert existential(member) == (["a", "b"], "0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ 10 = a * b")
    assert existential("⊢ ∃ x : ℕ, x * x = 49") == (["x"], "x * x = 49")
    assert existential("⊢ ∃ x : ℤ, x * x = 49") is None
    assert existential("k : ℕ\nh : 0 < k\n⊢ ∃ x, x * k = 49") is None  # the body names a variable
    assert existential("⊢ ∃ f : ℕ → ℕ, ∀ x, f x = x") is None
    src = witness_search_file("import Mathlib", ["a", "b"], "0 < a ∧ 10 = a * b")
    assert "for a in List.range" in src and "for b in List.range" in src and "decide (0 < a ∧ 10 = a * b)" in src
    assert read_witnesses([{"severity": "info", "data": "[[1, 10], [5, 2]]"}]) == [["1", "10"], ["5", "2"]]

    class ExistLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            if "List.range" in source and "decide (" in source:
                self.sources.append(source)
                return LeanCheck(True, [{"severity": "info", "data": "[[1, 10]]"}], False, False, 1)
            if "exact ⟨1, 10, by norm_num⟩" in source:
                return LeanCheck(True, [], "sorry" in source, False, 1)
            check = await super().check_file(source)
            msgs = [dict(m, data=m["data"].replace("⊢ demo", member))
                    if "unsolved" in str(m.get("data")) else m for m in check.messages]
            return LeanCheck(check.accepted, msgs, check.has_sorry, False, 1)
    lean, llm = ExistLean(), ScriptLLM({"model-a": ["have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert "exact ⟨1, 10, by norm_num⟩" in result.solution
    assert not llm.calls  # closed before any model was asked
    found = [e for e in result.metadata["events"] if e.get("kind") == "witnesses"]
    assert found and found[0]["found"] == [["1", "10"]] and found[0]["accepted"] is True


def test_a_stuck_leaf_inside_a_mostly_proved_have_is_restarted_before_the_have_is_withdrawn():
    # Measured on rmo_2000_6 (win54, 08:43): `have hmin : 10 ≤ a * b` held h2a,
    # h5a (both proved) and a 4-way case split with 2 cases closed; `inl.inl`
    # failed 4 times and the whole have went, proved work included. The board
    # then filled with `4 ≤ a + b`. A leaf whose have already holds proved facts
    # is restarted once (tries, feedback and plan cleared) before withdrawal.
    from submission.board.text import settled_inside
    from submission.board.types import Goal
    text = ("import Mathlib\n\ntheorem demo : True := by\n"
            "  have big : Q := by\n"
            "    have p1 : P := by\n      trivial\n"
            "    have p2 : P := by\n      trivial\n"
            "    have p3 : P := by\n      sorry\n"
            "    skip\n"
            "  trivial\n")
    assert settled_inside(text, Goal(11, "    ", "demo", "⊢ Q")) == 2
    assert settled_inside(text, Goal(10, "      ", "demo", "⊢ P")) == 0  # inside p3: nothing proved there
    assert settled_inside("import Mathlib\n\ntheorem demo : True := by\n  skip\n", Goal(4, "  ", "demo", "⊢ True")) == 0
    # end to end: two proved facts inside `big`, its own goal fails 4 times → restart, not withdraw
    script = ["have big : Q := by\n  have p1 : P := by\n    trivial\n  have p2 : P := by\n    trivial\n  sorry\nexact big"]
    script += [f"linarith [x{i}]" for i in range(9)] + ["exact big", "exact big", "exact big"]
    result, lean, llm, _ = run(ONE, {"model-a": script}, lines=("model-a",))
    kinds = [e.get("kind") for e in result.metadata["events"]]
    assert "leaf_restart" in kinds
    assert kinds.index("leaf_restart") < (kinds.index("withdraw") if "withdraw" in kinds else 10 ** 6)


def test_a_declaration_with_proved_facts_does_not_restart_while_its_last_goal_can_retry():
    # Measured on rmo_2000_6 (one55a): at 08:46 one goal was left under
    # `case inr.inr` inside `have h_min` (h2, h5, h2a, h5a proved above it);
    # it reached 6 tries and the whole declaration went back to its statement.
    from submission.board.text import settled_inside
    from submission.board.types import Goal
    text = ("import Mathlib\n\ntheorem demo : True := by\n"
            "  have big : Q := by\n"
            "    have p1 : P := by\n      trivial\n"
            "    have p2 : P := by\n      trivial\n"
            "    rcases h with h | h\n"
            "    case inl =>\n      trivial\n"
            "    case inr =>\n      skip\n"
            "  trivial\n")
    assert settled_inside(text, Goal(13, "      ", "demo", "case inr\n⊢ Q")) == 2
    script = ["have big : Q := by\n  have p1 : P := by\n    trivial\n  have p2 : P := by\n    trivial\n  sorry\nexact big"]
    script += [f"linarith [x{i}]" for i in range(14)] + ["exact big"] * 4
    result, lean, llm, _ = run(ONE, {"model-a": script}, lines=("model-a",), time_limit=60)
    kinds = [e.get("kind") or e.get("stage") for e in result.metadata["events"]]
    assert "leaf_restart" in kinds
    first_restate = kinds.index("restate") if "restate" in kinds else 10 ** 6
    assert kinds.index("leaf_restart") < first_restate


def test_the_challenge_imports_are_kept_and_numeral_exponents_typed_when_they_are_narrow():
    # Measured on rmo_2000_6 (one56a, 2026-09-03): the REPL and lake build
    # accepted the proof; the comparator scored 0 because under `import Mathlib`
    # `a ^ 2` elaborates through Monoid.npow, under the challenge's own imports
    # through instPowNat. Verified with the real comparator: original imports +
    # import Mathlib + `attribute [instance 2000] instPowNat` + `^ (2 : ℕ)` passes.
    from submission.contract import normalise_imports, type_exponents
    narrow = ("import Mathlib.Data.Nat.Basic\nimport Mathlib.Order.Bounds.Basic\n\n"
              "theorem t (a b : ℕ) : 2000 ∣ a ^ 2 * b ^ 5 → 10 ≤ a * b := by\n  sorry\n")
    out = normalise_imports(narrow, narrow)
    assert out.startswith("import Mathlib.Data.Nat.Basic\nimport Mathlib.Order.Bounds.Basic\nimport Mathlib\n\n"
                          "attribute [instance 2000] instPowNat\n\n")
    assert "2000 ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) → 10 ≤ a * b := by" in out
    assert normalise_imports(out, out) == out  # idempotent
    from submission.contract import statement_drift
    assert statement_drift(narrow, out) == []   # the agent's own grader accepts its header
    assert statement_drift(narrow, out.replace("10 ≤ a * b", "9 ≤ a * b"))
    full = "import Mathlib\n\ntheorem t (a : ℕ) : a ^ 2 = a * a := by\n  sorry\n"
    assert normalise_imports(full, full) == full  # a full-Mathlib challenge is untouched
    # exponents that are not numerals, and proof bodies, are left alone
    assert type_exponents("theorem t : 2 ^ n = 2 ^ n := by\n  have : 3 ^ 2 = 9 := by norm_num\n  rfl\n") \
        == "theorem t : 2 ^ n = 2 ^ n := by\n  have : 3 ^ 2 = 9 := by norm_num\n  rfl\n"


def test_a_board_that_accepts_nothing_for_a_share_of_the_window_restarts_before_the_counts_say_so(monkeypatch):
    # Measured on p09 (reg61b, 2026-09-03 10:14Z): 7 of 30 steps accepted, both
    # withdrawals on one route, and the clock ran out before every goal reached
    # LAST_IN_LINE. Time without an accepted step is a reason to start over.
    import submission.board_agent as ba
    from submission.run import blackboard
    clock = {"now": 0.0}

    def ticking():
        clock["now"] += 5.0
        return clock["now"]

    monkeypatch.setattr(ba.time, "monotonic", ticking)
    challenge = "import Mathlib\n\ntheorem demo (n : ℕ) : True := by\n  sorry\n"
    result, _, _, _ = run(challenge, {"model-b": ["linarith [h%d]" % i for i in range(40)]
                                      + ["have key : True := by trivial\nexact key"] * 3},
                          lines=("model-b",), time_limit=600.0)
    first = next(e for e in result.metadata["events"] if e.get("stage") == "restate")
    assert first["tries"] < blackboard.LAST_IN_LINE


def test_goal_tokens_are_the_goal_s_identifiers_then_its_notation_with_the_weak_words_last():
    from submission.board.probes import goal_tokens
    assert goal_tokens("hp : Nat.Prime p\n⊢ (2 ^ 2 * 1009 ^ 2).divisors.card = 9") == [
        "divisors", "pow", "nat", "prime"]
    assert goal_tokens("a b : ℕ\nhdiv : 2000 ∣ a ^ 2 * b ^ 5\n⊢ 10 ≤ a * b")[:2] == ["dvd", "pow"]
    assert goal_tokens("⊢ True") == []


def test_the_environment_s_answer_for_a_goal_s_words_reaches_the_step_prompt():
    # The curated sheets cover 13 vocabularies; a holdout goal outside them got
    # nothing. Lean scans its own constants for the goal's tokens instead.
    from submission.board.probes import goal_tokens
    challenge = ("import Mathlib\n\ntheorem demo (m n : ℕ) (h : m.Coprime n) : "
                 "(m * n).divisors.card = 1 := by\n  sorry\n")
    asked = []

    class LibraryLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            if "Library for this goal" in source:
                asked.append(source)
                return LeanCheck(True, [{"severity": "info", "data":
                                         "Library for this goal:\n  Nat.Coprime.card_divisors_mul : "
                                         "∀ {m n : ℕ}, m.Coprime n → (m * n).divisors.card = "
                                         "m.divisors.card * n.divisors.card"}], False, False, 1)
            check = await super().check_file(source, timeout_s)
            msgs = [dict(m, data=m["data"].replace("⊢ demo", "h : m.Coprime n\n⊢ (m * n).divisors.card = 1"))
                    if "unsolved" in str(m.get("data")) else m for m in check.messages]
            return LeanCheck(check.accepted, msgs, check.has_sorry, False, 1)

    lean, llm = LibraryLean(), ScriptLLM({"model-a": ["linarith [a]",
                                                        "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    asyncio.run(agent.solve(Problem(id="demo", description="prove it", challenge=challenge),
                            FakeServices(lean, llm)))
    assert len(asked) == 1 and '"coprime"' in asked[0] and '"divisors"' in asked[0]
    # The scan waits for one rejected step (measured: 269 scans at 22 s each
    # over 70 runs); the sheet is in the prompt that follows the rejection.
    prompts = [p for m, p in llm.calls if "Names the loaded Mathlib has" in p]
    assert "Nat.Coprime.card_divisors_mul" not in llm.calls[0][1]
    assert any("Nat.Coprime.card_divisors_mul" in p for p in prompts)


def test_a_stalled_board_takes_back_the_innermost_open_have_before_it_restarts_the_declaration(monkeypatch):
    # Undo at the goal, not the declaration: the facts beside the stuck `have`
    # stay on the board, and only when no open goal sits inside a `have` does
    # the declaration go back to its statement.
    import submission.board_agent as ba
    clock = {"now": 0.0}

    def ticking():
        clock["now"] += 12.0
        return clock["now"]

    monkeypatch.setattr(ba.time, "monotonic", ticking)
    challenge = "import Mathlib\n\ntheorem demo (n : ℕ) : True := by\n  sorry\n"
    result, _, _, _ = run(challenge, {"model-b": ["have inner : True := by\n  sorry\nexact inner"]
                                      + ["linarith [h%d]" % i for i in range(40)]
                                      + ["have key : True := by trivial\nexact key"] * 3},
                          lines=("model-b",), time_limit=900.0)
    kinds = [(e.get("kind") or e.get("stage"), e.get("by")) for e in result.metadata["events"]]
    first_withdraw = next((i for i, k in enumerate(kinds) if k == ("withdraw", "harness")), None)
    first_restate = next((i for i, k in enumerate(kinds) if k[0] == "restate"), len(kinds))
    assert first_withdraw is not None and first_withdraw < first_restate


def test_the_stall_take_back_happens_on_a_fork_so_the_stuck_subtree_stays_a_branch(monkeypatch):
    # OR below the root: the board with the stuck have and the board without it
    # race as two branches, the way two plans do.
    import submission.board_agent as ba
    clock = {"now": 0.0}

    def ticking():
        clock["now"] += 12.0
        return clock["now"]

    monkeypatch.setattr(ba.time, "monotonic", ticking)
    challenge = "import Mathlib\n\ntheorem demo (n : ℕ) : True := by\n  sorry\n"
    result, _, _, _ = run(challenge, {"model-b": ["have inner : True := by\n  sorry\nexact inner"]
                                      + ["linarith [h%d]" % i for i in range(40)]
                                      + ["have key : True := by trivial\nexact key"] * 3},
                          lines=("model-b",), time_limit=900.0)
    events = result.metadata["events"]
    fork = next((i for i, e in enumerate(events) if e.get("stage") == "fork" and e.get("why") == "stall"), None)
    withdraw = next((i for i, e in enumerate(events) if e.get("kind") == "withdraw" and e.get("by") == "harness"), None)
    assert fork is not None and withdraw is not None and fork < withdraw


def test_the_audit_switch_lets_a_false_claim_in_when_off():
    # The ablation arm: VM_AUDIT=off. The same false `have` the audit refutes
    # in test_a_claim_that_enters_through_a_prefix_cut_is_audited_too goes in.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["have bad : x = 3 := by\n  sorry\nlinarith",
                    "have key : True := by trivial\nexact key"] * 2})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    assert not any(e.get("kind") == "audit" for e in result.metadata["events"])


def test_a_false_claim_is_refuted_by_evaluation_before_any_auditor_is_asked():
    # Measured on rmo_2000_2: `(x+2)^3 < y^3 ↔ x ≥ 9` is false at x = 9, y = 11,
    # the auditor never named those values, and the board built on it for an hour.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"

    class SearchLean(WitnessLean):
        async def check_file(self, source, timeout_s=None):
            if "List.range" in source and "decide (" in source and "¬ (" in source:
                self.sources.append(source)
                return LeanCheck(True, [{"severity": "info", "data": "[[0]]"}], False, False, 1)
            return await super().check_file(source, timeout_s)

    lean, llm = SearchLean(), ScriptLLM({
        "model-a": ["have bad : x = 3 := by\n  sorry\nlinarith",
                    "have key : True := by trivial\nexact key",
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    audits = [e for e in result.metadata["events"] if e.get("kind") == "audit"]
    assert audits and audits[0]["verdict"] == "refuted" and audits[0]["by"] == "evaluation"
    assert audits[0]["values"] == {"x": "0"}
    assert not any(p.startswith("A goal inside a Lean 4 proof, exactly as Lean states it") for _, p in llm.calls)
    assert "have bad" not in result.solution
    search = [src for src in lean.sources if "List.range" in src][0]
    assert "(x < 2)" in search and "¬ (x = 3)" in search


def test_a_fact_posted_under_an_intro_stays_where_its_hypotheses_are():
    # Measured on rmo_2000_2 (v7.66): `y^3 < (x+2)^3`, true under `intro hxle`
    # (x ≤ 8), was lifted above `h1`, refuted at (9, 11) as a global claim, and
    # the correct route was withdrawn with it. A lift may not drop context.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    result, lean, llm, _ = run(challenge, {
        "model-a": ["have outer : True := by\n  sorry\nexact outer",
                    "intro loc\nhave inner : 1 = 1 := by\n  sorry\nhave key : True := by trivial\nexact key",
                    "have key2 : True := by trivial\nexact key2"]}, lines=("model-a",))
    text = result.solution
    assert "have inner" in text and text.index("intro loc") < text.index("have inner")
    assert text.index("have outer") < text.index("have inner")
    assert not any(e.get("kind") == "lifted" for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True
    # The same when the `intro` was written a step earlier and is on the board.
    result, lean, llm, _ = run(challenge, {
        "model-a": ["have outer : True := by\n  sorry\nexact outer", "intro loc",
                    "have inner : 1 = 1 := by\n  sorry\nhave key : True := by trivial\nexact key",
                    "have key2 : True := by trivial\nexact key2"]}, lines=("model-a",))
    text = result.solution
    assert text.index("have outer") < text.index("intro loc") < text.index("have inner")
    assert not any(e.get("kind") == "lifted" for e in result.metadata["events"])


def test_an_auditor_that_does_not_answer_in_time_lets_the_step_through_unverified():
    # Measured on putnam_2020_a2 (v7.63): one audit reply took 482 s under the
    # board lock, the run's only gap over 90 s. The call is not cancelled (an
    # open reservation fails the problem); it is drained before the agent returns.
    import submission.board_agent as ba
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = WitnessLean(), ScriptLLM({
        "model-a": ["have fine : x < 3 := by\n  sorry\nhave key : True := by trivial\nexact key",
                    "omega", "have key : True := by trivial\nexact key"],
        "model-b": ['{"holds": true}'] * 4}, delay={"model-b": 0.8})
    from submission.run import asking
    was = asking.AUDIT_WAIT_S
    asking.AUDIT_WAIT_S = 0.1
    try:
        agent = BoardAgent(Config(lines=("model-a", "model-b"), budget_usd=1.0, time_limit_s=600.0))
        started = time.monotonic()
        result = asyncio.run(agent.solve(
            Problem(id="demo", description="prove it", challenge=challenge),
            FakeServices(lean, llm)))
        wall = time.monotonic() - started
    finally:
        asking.AUDIT_WAIT_S = was
    events = result.metadata["events"]
    slow = [e for e in events if e.get("kind") == "slow_call"]
    assert slow and slow[0]["by"] == "model-b" and slow[0]["audits"] == 1
    audit = next(e for e in events if e.get("kind") == "audit" and "x < 3" in e.get("goal", ""))
    assert audit["verdict"] == "unverified"
    assert "have fine" in result.solution and result.metadata["accepted_by_repl"] is True
    # The late reply was still awaited: the run took at least the auditor's delay.
    assert wall >= 0.8, wall


def test_a_rejected_reply_is_read_for_the_statements_it_makes():
    # Measured on putnam_2018_a1 (v7.74): 30 replies called the divisor technique
    # and none reached Lean, each call below the first error of a long reply.
    # The statements of a rejected block go on the board as facts to prove.
    from submission.board.reply import mine_statements
    block = ("linarith\nhave a : True := by\n  trivial\nhave b : 1 = 1 := by rfl\n"
             "have a : 2 = 2 := by rfl\nintro loc\nhave c : True := by trivial\n")
    assert mine_statements(block, {}, []) == ["have a : True := by", "have b : 1 = 1 := by"]
    assert mine_statements(block, {"True": "k"}, ["1 = 1"]) == ["have a : 2 = 2 := by"]
    result, lean, llm, _ = run(ONE, {
        "model-a": ["linarith\nhave a : True := by\n  trivial\nhave b : 1 = 1 := by rfl\nexact a",
                    "exact a", "have k : True := by trivial\nexact k", "have k : True := by trivial\nexact k"]},
        lines=("model-a",))
    events = result.metadata["events"]
    mined = [e for e in events if e.get("kind") == "mined"]
    assert mined and mined[0]["facts"] == 2
    proofs = [src.split("theorem demo", 1)[1] for src in lean.sources if "theorem demo" in src]
    assert any("have a : True := by" in p and "have b : 1 = 1 := by" in p and "linarith" not in p
               for p in proofs)


def test_leaf_candidates_are_built_from_the_goal_s_shape_and_tried_before_any_model():
    # Measured on 3 September: rmo_2000_2, rmo_2001_2 and putnam_2018_a1 had the
    # route on the board within minutes and were lost on leaves of these shapes.
    from submission.leaves import leaf_candidates
    crux = ("x y : ℕ\nhx : 0 < x\nhy : 0 < y\nh : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8\n"
            "hxge : x ≥ 9\n⊢ y = x + 2")
    got = leaf_candidates(crux)
    assert got[0].endswith("(pow_squeeze y 3 (x + 2) with hxge)") and any("Nat.exists_eq_add_of_le hxge" in c for c in got)
    assert not any(c.endswith("with hx") or c.endswith("with hy") for c in got)
    dvd = "m p q : ℕ\nhp : Nat.Prime p\nhA_dvd : m - (p + q) ∣ 5 * p * q\n⊢ m - (p + q) = 1 ∨ m - (p + q) = 5"
    assert any(c.startswith("set_option maxHeartbeats 400000 in (prime_facts; divisor_cases hA_dvd <;> (first | (solve_sub; first | (simp only")
               for c in leaf_candidates(dvd))
    assert leaf_candidates("⊢ True") == []
    small = "x : ℕ\nhb : x ≤ 3\nh : x ^ 2 = 4\n⊢ x = 2"
    assert any("interval_cases x <;>" in c for c in leaf_candidates(small))
    assert any("bounded_cases x 3" in c for c in leaf_candidates(small))

    class LeafLean(BoardLean):
        """The theorem's own goal carries `hb : x ≤ 3`; `interval_cases x` closes it."""
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source)
            if "interval_cases x" in source and "theorem demo" in source:
                return LeanCheck(True, [], False, False, 1)
            msgs = [dict(m, data=m["data"].replace("⊢ demo", "hb : x ≤ 3\n⊢ x = 2"))
                    if "⊢ demo" in str(m.get("data")) else m for m in check.messages]
            return LeanCheck(check.accepted, msgs, check.has_sorry, False, 1)

    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hb : x ≤ 3) : x = 2 := by\n  sorry\n"
    lean, llm = LeafLean(), ScriptLLM({"model-a": ["omega"] * 3})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=challenge),
                                     FakeServices(lean, llm)))
    leaf = [e for e in result.metadata["events"] if e.get("kind") == "leaf"]
    assert leaf and leaf[0]["accepted"] and "interval_cases x" in leaf[0]["block"]
    assert not any(p.startswith("A goal inside a Lean 4 proof, exactly as Lean states it") for _, p in llm.calls)
    assert "interval_cases x" in result.solution


def test_a_claim_the_walk_covers_is_settled_without_an_auditor_call():
    # Measured over 7 runs: every refutation with ℕ binders came from the walk,
    # the auditor's came from closed claims and ℤ, and audit calls were half of
    # all calls (108 of 285 on putnam_2020_a2, one reply 482 s under the lock).
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"

    class CleanSearchLean(WitnessLean):
        async def check_file(self, source, timeout_s=None):
            if "List.range" in source and "decide (" in source and "¬ (" in source:
                self.sources.append(source)
                return LeanCheck(True, [{"severity": "info", "data": "[]"}], False, False, 1)
            return await super().check_file(source, timeout_s)

    lean, llm = CleanSearchLean(), ScriptLLM({
        "model-a": ["have fine : x < 3 := by\n  sorry\nhave key : True := by trivial\nexact key",
                    "omega", "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="prove it", challenge=challenge),
        FakeServices(lean, llm)))
    audits = [e for e in result.metadata["events"] if e.get("kind") == "audit" and "x < 3" in e.get("goal", "")]
    assert audits and audits[0]["verdict"] == "holds" and audits[0]["by"] == "evaluation"
    assert not any(p.startswith("A goal inside a Lean 4 proof, exactly as Lean states it") for _, p in llm.calls)
    assert "have fine" in result.solution


def test_the_technique_preamble_sits_after_the_header_and_the_models_are_told_about_it():
    # Techniques are Lean tactics defined once in the file, not prose recipes:
    # checked once in the image, callable by either model anywhere in the file.
    from submission.contract import normalise_imports, with_preamble
    from submission.techniques import PREAMBLE_MARK
    narrow = ("import Mathlib.Data.Nat.Basic\n\ntheorem demo (d : ℕ) (h : d ∣ 2000) : 5 ≤ d := by\n  sorry\n")
    text = with_preamble(normalise_imports(narrow, narrow))
    lines = text.split("\n")
    assert lines[0] == "import Mathlib.Data.Nat.Basic" and lines[1] == "import Mathlib"
    assert lines.index("attribute [instance 2000] instPowNat") < lines.index(PREAMBLE_MARK) < lines.index(
        "theorem demo (d : ℕ) (h : d ∣ 2000) : 5 ≤ d := by")
    assert 'syntax "divisor_cases" ident : tactic' in text and "elab_rules" in text and with_preamble(text) == text
    # A hoisted lemma, a probe or a set_option lands below the technique block,
    # else a lemma that calls a technique is written above its definition.
    from submission.framework import insert_preamble
    from submission.techniques import PREAMBLE_END
    hoisted = insert_preamble(text, "lemma aux : True := by\n  sorry")
    assert hoisted.index(PREAMBLE_END) < hoisted.index("lemma aux") < hoisted.index("theorem demo")
    # The finishing tidy (lighten, prune) measures the proof, not the file: the
    # block is the same size in every file and a short proof must not be pruned.
    from submission.framework_agent import below_header, TIDY_ABOVE_BYTES
    assert len(text) > TIDY_ABOVE_BYTES // 2 and len(below_header(text)) < 200
    result, lean, llm, _ = run(ONE, {"model-a": ["have key : True := by trivial\nexact key"] * 2},
                               lines=("model-a",))
    # A check carries the block only when the proof calls a technique (measured
    # on a 4-core pod: 1.5 s a check with it, 0.05 s without), its lines blanked
    # otherwise so Lean's line numbers still map; the delivered file of a proof
    # that calls none drops it.
    checks = [src for src in lean.sources if "have key" in src]
    assert checks and not any("divisor_cases" in src for src in checks)
    assert "divisor_cases" not in result.solution
    assert any("`divisor_cases h`" in s for s in llm.systems)
    from submission.techniques import blank_techniques
    kept = blank_techniques(text.replace("sorry", "divisor_cases h"))
    assert "elab_rules" in kept and blank_techniques(text).count("\n") == text.count("\n")
    assert "elab_rules" not in blank_techniques(text)
    # Lean sees the block; a model sees one comment line in its place. Measured:
    # 4.6 KB of elab code sat in every step and audit prompt of three runs.
    assert not any("elab_rules" in p or "macro_rules" in p for _, p in llm.calls)
    assert any("tactics defined for this file" in p for _, p in llm.calls)


def test_apply_suggestions_close_a_goal_without_a_model_or_reach_the_prompt():
    # Measured in the image: `apply?` closed 4 of 4 leaf goals by `exact`
    # (Nat.le_of_dvd, Nat.Prime.dvd_of_dvd_pow, Nat.sum_range_choose,
    # lt_of_pow_lt_pow_left'), names the models write wrong or never reach.
    class ApplyLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            if "apply?" in source:
                self.sources.append(source)
                rows = source.split("\n")
                # The REPL numbers lines in the import-stripped body.
                line = next(i for i, l in enumerate(rows, start=1) if "apply?" in l) - sum(
                    1 for l in rows if l.startswith("import "))
                return LeanCheck(False, [{"severity": "info", "pos": {"line": line}, "endPos": {"line": line},
                                          "data": "Try this:\n  [apply] exact le_of_dvd hb h"}],
                                 False, False, 1)
            if "exact le_of_dvd hb h" in source:
                # Real Lean: the exact closes the goal; `skip` on no goals is silent.
                return LeanCheck(True, [], "sorry" in source, False, 1)
            return await super().check_file(source, timeout_s)

    lean, llm = ApplyLean(), ScriptLLM({"model-a": ["linarith [a]"] * 3})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert "exact le_of_dvd hb h" in result.solution
    lib = [e for e in result.metadata["events"] if e.get("kind") == "library"]
    assert lib and lib[0]["accepted"] and lib[0]["found"] == 1
    # Measured over 70 runs: `apply?` and the name scan were 19% of the wall
    # clock under the lock, 22 goals closed in 601 probes. They wait for one
    # rejected step; a goal the first step closes never pays for them.
    first_probe = next(i for i, src in enumerate(lean.sources) if "apply?" in src)
    first_step = next(i for i, src in enumerate(lean.sources) if "\n  linarith [a]" in src)
    assert first_step < first_probe
    assert not any("Library for this goal" in p or "Names the loaded Mathlib" in p
                   for _, p in llm.calls[:1])


def test_a_placeholder_left_under_a_closing_step_is_dropped_not_reused():
    # Measured on rmo_2000_6 (v7.74, 5 of 6 runs lost): a step that closed a
    # nested goal left its trailing `sorry` behind; rendered as `skip` it was
    # silent, took the enclosing block's goal for its own text, and every later
    # step for that goal was written at the dead line ("no goals left where
    # that step was written", nine times over).
    nest = ("import Mathlib\n\ntheorem demo : True := by\n  have h : P := by\n"
            "    sorry\n  sorry\n")
    result, lean, llm, _ = run(nest, {"model-a": ["exact h", "exact h", "exact h"]},
                               lines=("model-a",), time_limit=20)
    proof = result.solution.split("theorem demo", 1)[1]
    assert result.metadata["accepted_by_repl"] is True
    assert proof == " : True := by\n  have h : P := by\n    exact h\n  exact h\n"
    assert not any("no goals left where that step was written" in p
                   for _, p in llm.calls)


def test_a_finished_proof_that_calls_no_technique_ships_without_the_block():
    # The judge compiles the solution cold (180 s, 4 cores); the technique
    # block is 6.8 KB of elab code that a proof of `True` never needs.
    result, lean, llm, _ = run(ONE, {"model-a": ["have key : True := by trivial\nexact key"]},
                               lines=("model-a",), time_limit=20)
    assert result.metadata["accepted_by_repl"] is True
    assert "techniques defined for this file" not in result.solution
    assert "divisor_cases" not in result.solution
    verify = next(e for e in result.metadata["events"] if e.get("stage") == "verify")
    assert verify["techniques"] == "dropped"
    # A proof that calls one keeps the block (the fake accepts any `exact key`).
    result2, _, _, _ = run(ONE, {"model-a": ["have key : True := by divisor_cases h\nexact key"]},
                           lines=("model-a",), time_limit=20)
    assert result2.metadata["accepted_by_repl"] is True
    assert "techniques defined for this file" in result2.solution


def test_powers_bounded_in_the_context_give_a_pow_bounds_leaf():
    # Measured on rmo_2000_2 (v7.79): the route left the bounds on `P` with
    # `h : y ^ 3 = P` and a disjunction goal; the squeeze leaf expects `y = E`.
    from submission.leaves import leaf_candidates
    goal = ("x y : ℕ\nh : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8\n"
            "h_up : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 ≤ (x + 3) ^ 3\n"
            "h_low : (x + 2) ^ 3 ≤ x ^ 3 + 8 * x ^ 2 - 6 * x + 8\n⊢ y = x + 2 ∨ y = x + 3")
    blocks = [c.split("\n")[-1] for c in leaf_candidates(goal)]
    assert blocks[0].endswith("(pow_bounds y 3)") and not any("pow_bounds x" in b for b in blocks)
    direct = "a b : ℕ\nh1 : (b + 1) ^ 2 ≤ a ^ 2\nh2 : a ^ 2 < (b + 3) ^ 2\n⊢ b + 1 ≤ a ∧ a ≤ b + 2"
    assert [c for c in leaf_candidates(direct)] == ["set_option maxHeartbeats 400000 in (pow_bounds a 2)"]
    assert not any("pow_bounds" in c for c in leaf_candidates("n : ℕ\n⊢ 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n"))


def test_an_upper_bound_on_the_variable_under_a_power_gets_the_contradiction_squeeze():
    # Measured on rmo_2000_2 (v7.79, h78r1): at 20:28 the board was one goal
    # short, `h_bound : x ≤ 9`, and stayed so; for x ≥ 10 the cube sits
    # strictly between (x+2)³ and (x+3)³, and 2 is 8 // 3 from P's second term.
    from submission.leaves import leaf_candidates, _shifts
    assert _shifts("x ^ 3 + 8 * x ^ 2 - 6 * x + 8", 3) == ["x + 2"]
    assert _shifts("x ^ 3 + 9 * x ^ 2 + 1", 3) == ["x + 3", "x + 2"]
    assert _shifts("x ^ 2 + x + 5", 2) == [] and _shifts("11", 3) == []
    ctx = "x y : ℕ\nhx : 0 < x\nhy : 0 < y\nh : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8\n"
    blocks = leaf_candidates(ctx + "⊢ x ≤ 9")
    assert blocks[0].endswith("(by_contra hc; push_neg at hc; pow_squeeze y 3 (x + 2) with hc)")
    # `hyx : y = x + 2 ⊢ x = 9`: substitute, make the ℕ subtraction exact, arithmetic.
    blocks = leaf_candidates(ctx + "hyx : y = x + 2\n⊢ x = 9")
    assert any(b.startswith("set_option maxHeartbeats 400000 in (subst hyx; nat_sub_exact; first | (simp only")
               for b in blocks[:2])
    # Under the contradiction hypothesis the squeeze uses it as the lower bound.
    blocks = leaf_candidates("x y : ℕ\nhc : 9 < x\nh : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8\n⊢ False")
    assert "pow_squeeze y 3 (x + 2) with hc" in blocks[0]


def test_a_claim_that_holds_only_past_a_threshold_is_split_there():
    # Measured on rmo_2000_2 (v7.84, second run, 0 at 2612 s): the models
    # posted `(x + 2) ^ 3 ≤ y ^ 3` and `y ≤ x + 2` with no case split; both
    # hold from x = 10 on (P − (x+2)³ = 2x(x−9)) and below that the equation
    # y³ = P has no solution, which cases over x then y establish.
    from submission.leaves import leaf_candidates, _threshold, _evaluate
    assert _evaluate("x ^ 3 + 8 * x ^ 2 - 6 * x + 8", "x", 9) == 1331
    assert _evaluate("x - 5", "x", 3) == 0                       # ℕ subtraction truncates
    assert _threshold("x ^ 3 + 8 * x ^ 2 - 6 * x + 8", "x + 2", 3, "x") == 10
    assert _threshold("x ^ 3 + 8 * x ^ 2 - 6 * x + 8", "x + 3", 3, "x") is None
    ctx = "x y : ℕ\nhx : 0 < x\nhy : 0 < y\nh : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8\n"
    for target in ("⊢ (x + 2) ^ 3 ≤ y ^ 3", "⊢ y ≤ x + 2", "⊢ x + 2 ≤ y"):
        block = leaf_candidates(ctx + target)[0]
        assert block.startswith("set_option maxHeartbeats 400000 in (rcases Nat.lt_or_ge x 10 with hlt | hge <;> "
                                "[(interval_cases x <;> first | omega | (bounded_cases y 13)); (obtain")
    assert not any("rcases Nat.lt_or_ge" in c for c in leaf_candidates(ctx + "⊢ y ^ 3 < (x + 3) ^ 3"))


def test_environment_scans_stop_when_they_have_had_their_share_of_the_clock():
    # Measured on a 4-core pod (rmo_2000_6, v7.85): 425 Lean checks, 2443 s of
    # 2642 s in Lean, the name scan 689 s and apply? with the vocabulary scan
    # 478 s of it, 91 model calls in 44 minutes. A slow machine gets the probes
    # it can afford: each kind stops past PROBE_SHARE of the elapsed clock.
    class SlowScanLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            if "apply?" in source or "Library for this goal" in source:
                self.sources.append(source)
                return LeanCheck(False, [], False, False, 100_000)      # 100 s each
            return await super().check_file(source, timeout_s)

    two = ("import Mathlib\n\ntheorem demo : True := by\n  have a : P := by\n    sorry\n"
           "  have b : Q := by\n    sorry\n  have c : R := by\n    sorry\n  sorry\n")
    lean = SlowScanLean()
    llm = ScriptLLM({"model-a": ["linarith [x]"] * 40})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=3.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=two),
                                     FakeServices(lean, llm)))
    scans = [s for s in lean.sources if "apply?" in s or "Library for this goal" in s]
    skipped = [e for e in result.metadata["events"] if e.get("stage") == "probe_skipped"]
    assert len(scans) == 1 and skipped and skipped[0]["kind"] == "scan"


def test_a_disjunction_of_subtraction_equations_is_split_and_each_case_solved():
    # Measured on rmo_2001_2 (v7.87): divisor_cases put the eight-way fact on
    # the board four times and the models never split it inside the clock.
    from submission.leaves import leaf_candidates
    goal = ("p q m : ℕ\nhp : Nat.Prime p\nhq : Nat.Prime q\n"
            "h_factor : (m - p - q) * (m + p + q) = 5 * p * q\n"
            "hA : m - p - q = 1 ∨ m - p - q = 5 ∨ m - p - q = p ∨ m - p - q = p * q\n"
            "⊢ p = q ∨ p = 3 ∧ q = 11 ∨ p = 11 ∧ q = 3")
    blocks = leaf_candidates(goal)
    assert blocks[0].startswith("set_option maxHeartbeats 400000 in (prime_facts; rcases hA with hc | hc | hc | hc <;> (solve_sub; first | (simp only")
    assert "interval_cases p <;> interval_cases q" in blocks[0]      # (p-2)(q-2) = 9 needs the pair search
    assert not any("0 < (1 ∨" in b for b in blocks)      # the disjunction is not read as one equation


def test_a_disjunction_of_values_is_substituted_case_by_case():
    # Measured on putnam_2018_a1 (v7.88): divisor_cases over ℤ left
    # `a = 673 ∨ a = 674 ∨ ...` on the board with the membership goal open.
    from submission.leaves import leaf_candidates
    goal = ("a b : ℤ\nh_eq : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2\n"
            "ha : a = 673 ∨ a = 674 ∨ a = 1009\n⊢ (a, b) ∈ {(673, 1358114), (674, 340033), (1009, 2018)}")
    blocks = leaf_candidates(goal)
    assert blocks[0].startswith("set_option maxHeartbeats 400000 in (rcases ha with rfl | rfl | rfl <;> (first | (simp only")
    assert "norm_num [Set.mem_insert_iff" in blocks[0]


def test_the_closing_chain_normalises_membership_and_substitutes_before_it_tries_nlinarith():
    # Measured on putnam_2018_a1 (v7.90, image): after `divisor_cases h_dvd`
    # the pair-membership case closes only once `simp_all` has rewritten
    # `h_factorized` with the case value (then omega finds b); the old chain
    # reached neither, and its failing `omega`/`nlinarith` tries ahead of the
    # membership simp burned the theorem's 200000 heartbeats.
    from submission.leaves import leaf_candidates
    goal = ("a b : ℤ\nh_factorized : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2\n"
            "h_x_pos : 3 * a - 2018 > 0\nh_dvd : 3 * a - 2018 ∣ 2018 ^ 2\n"
            "⊢ (a, b) ∈ {(673, 1358114), (674, 340033), (1009, 2018)}")
    block = next(b for b in leaf_candidates(goal) if "divisor_cases h_dvd" in b)
    chain = block.split("divisor_cases h_dvd <;> (first | (solve_sub; ", 1)[1]
    assert chain.startswith("first | (simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq, "
                            "Finset.mem_insert, Finset.mem_singleton] at *; first | omega | (simp_all <;> omega)) | omega")
    assert chain.index("(simp_all <;> omega)") < chain.index("nlinarith")


def test_a_hypothesis_lean_prints_over_several_lines_is_still_read():
    # Measured on rmo_2001_2 (v7.91, r3): the eight-way divisor fact was on the
    # board as `h_cases :⏎  m - p - q = 1 ∨⏎    m - p - q = 5 ∨ ...` and the
    # rcases leaf, which closes the goal in the image, was never generated.
    from submission.leaves import _hyps, leaf_candidates
    goal = ("p q : ℕ\nhp : Nat.Prime p\nhq : Nat.Prime q\nm : ℕ\n"
            "h_factor : (m - p - q) * (m + p + q) = 5 * p * q\n"
            "h_cases :\n  m - p - q = 1 ∨\n    m - p - q = 5 ∨\n"
            "      m - p - q = p ∨ m - p - q = q ∨ m - p - q = 5 * p ∨ m - p - q = 5 * q ∨ m - p - q = p * q ∨ m - p - q = 5 * p * q\n"
            "⊢ p = q ∨ p = 3 ∧ q = 11 ∨ p = 11 ∧ q = 3")
    assert dict(_hyps(goal))["h_cases"].startswith("m - p - q = 1 ∨ m - p - q = 5 ∨ m - p - q = p ∨")
    assert any("rcases h_cases with hc | hc | hc | hc | hc | hc | hc | hc <;> (solve_sub;" in b
               for b in leaf_candidates(goal))


def test_an_old_lean_container_is_renewed_while_a_model_is_being_waited_on(monkeypatch):
    # Measured (win, harness image, --memory 5g): the REPL keeps ~46–77 MB per
    # check of a real board (a trivial file keeps nothing), so it is OOM-killed
    # after 55–90 checks; 28 kills in three hours across the lanes, each costing
    # the check in flight plus a cold import. The renewal happens on our terms,
    # under a model wait, before the kernel does it mid-check.
    import submission.board_agent as ba

    class AgedLean(BoardLean):
        def __init__(self):
            super().__init__()
            self.starts = 0
            self._container_name = "re-takehome-repl-test"

        def close(self):
            pass

        def start(self):
            self.starts += 1

    monkeypatch.setattr(ba, "RENEW_AFTER_CHECKS", 3)
    monkeypatch.setattr(ba, "container_memory_bytes", lambda name: None)
    lean, llm = AgedLean(), ScriptLLM({
        "model-a": ["no", "have key : True := by trivial", "exact key"],
        "model-b": ["no", "have key : True := by trivial", "exact key"]})
    agent = BoardAgent(Config(lines=("model-a", "model-b"), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=TWO),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    assert lean.starts >= 1
    assert any(e.get("stage") == "renew" for e in result.metadata["events"])


def test_a_power_with_a_literal_base_under_a_modulus_gets_the_cycle_leaf():
    # Measured on p09 (v7.91–v7.93, five failing runs): `2 ^ n % 7 = 1` or
    # `3 ∣ n` was withdrawn after four tries and the run restarted from the
    # skeleton each time; the periodicity is one lemma and a case split.
    from submission.leaves import leaf_candidates
    from submission.techniques import uses_techniques, preamble
    goal = "n : ℕ\nhn : 0 < n\nh3 : 3 ∣ n\n⊢ 2 ^ n % 7 = 1"
    assert leaf_candidates(goal)[0] == "set_option maxHeartbeats 400000 in (pow_cycle 2 7 3 n)"
    both = leaf_candidates("n : ℕ\nhn : 0 < n\n⊢ 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n")
    assert any("pow_cycle 2 7 3 n" in b for b in both)
    assert any("pow_cycle 3 10 4 n" in b for b in leaf_candidates("n : ℕ\n⊢ 3 ^ n % 10 = 1 ∨ 3 ^ n % 10 = 3"))
    assert not any("pow_cycle" in b for b in leaf_candidates("n : ℕ\n⊢ 2 ^ n % 8 = 0"))   # no cycle
    assert not any("pow_cycle" in b for b in leaf_candidates("n : ℤ\n⊢ 2 ^ n % 7 = 1"))   # ℕ only
    assert uses_techniques(preamble() + "\ntheorem t (n : ℕ) : 2 ^ n % 7 = 1 := by\n  pow_cycle 2 7 3 n\n")


def test_a_product_equation_gives_the_divisor_leaf_without_a_divisibility_hypothesis():
    # Measured on the v7.93 repeats (r1): putnam_2018_a1 0 with h_factored on
    # the board and no `∣` step (the model bounded a instead, 15 leaf tries on
    # the membership goal, none fired), rmo_2001_2 likewise; in the image the
    # divisor block closes both from the product equation alone.
    from submission.leaves import leaf_candidates
    goal = ("a b : ℤ\nh_factorized : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2\n"
            "h_x_pos : 3 * a - 2018 > 0\n⊢ (a, b) ∈ {(673, 1358114), (674, 340033)}")
    blocks = leaf_candidates(goal)
    assert any("have hdvd : 3 * a - 2018 ∣ 2018 ^ 2 := Dvd.intro _ h_factorized; divisor_cases hdvd <;>" in b
               for b in blocks)
    assert any("have hdvd : 3 * b - 2018 ∣ 2018 ^ 2 := Dvd.intro_left _ h_factorized; divisor_cases hdvd <;>" in b
               for b in blocks)
    rmo = ("p q m : ℕ\nhp : Nat.Prime p\nhq : Nat.Prime q\n"
           "h_factor : (m - p - q) * (m + p + q) = 5 * p * q\n⊢ p = q ∨ p = 3 ∧ q = 11 ∨ p = 11 ∧ q = 3")
    assert any("prime_facts; have hdvd : m - p - q ∣ 5 * p * q := Dvd.intro _ h_factor; divisor_cases hdvd" in b
               for b in leaf_candidates(rmo))


def test_an_open_helper_nothing_graded_uses_does_not_hold_a_finished_proof_back():
    # Measured on p09 (v7.95, reg95 p09c): both graded theorems closed by the
    # pow_cycle leaf at 4 s each, but a shared lemma a model had proposed
    # (`mod7_pow2_cases`, never referenced) still carried a sorry, so the run
    # kept working that lemma for 10 more minutes and delivered best_effort.
    result, lean, llm, _ = run(ONE, {
        "model-a": ["no", "lemma stuck_helper (n : ℕ) : n = n := by\n  rfl"]
                   + ["have key : True := by trivial", "exact key"] * 4,
        "model-b": ["no"] + ["have key : True := by trivial", "exact key"] * 4}, time_limit=60.0)
    assert result.metadata["solved_by"] == "board_loop"
    assert "sorry" not in result.solution and "stuck_helper" not in result.solution
    assert any(e.get("stage") == "shed" and e.get("name") == "stuck_helper" for e in result.metadata["events"])


def test_a_check_issued_during_a_renewal_waits_for_the_new_container():
    # Measured on v7.96 (win, reg96 p10 and p09a, h96 rmo_2001_2): the renewal
    # swapped containers in a thread while another line's check went straight
    # to the kernel, so that check ran on a REPL without Mathlib (unknown
    # tactic, ℕ unbound) or raised LeanRuntimeError and the run aborted.
    from types import SimpleNamespace
    import submission.board_agent as ba

    class SwappingLean:
        def __init__(self):
            self.alive = True
            self.during_swap = 0
            self._container_name = "re-takehome-repl-test"

        def close(self):
            self.alive = False

        def start(self):
            time.sleep(0.2)
            self.alive = True

        async def check_file(self, source, timeout_s=None):
            await asyncio.sleep(0.05)
            if not self.alive:
                self.during_swap += 1
            return SimpleNamespace(accepted=self.alive, messages=[], container_restarted=False)

    async def scenario():
        inner = SwappingLean()
        lean = ba.RenewingLean(inner, [])
        lean.renew()
        check = await lean.check_file("theorem t : True := trivial")
        return inner, check

    inner, check = asyncio.run(scenario())
    assert inner.during_swap == 0
    assert check.accepted


PRODUCT = ("import Mathlib\n\ntheorem demo (p q m : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)\n"
           "    (h_factor : (m - p - q) * (m + p + q) = 5 * p * q) :\n"
           "    p = q ∨ p = 3 ∧ q = 11 ∨ p = 11 ∧ q = 3 := by\n  sorry\n")
PRODUCT_GOAL = ("p q m : ℕ\nhp : Nat.Prime p\nhq : Nat.Prime q\n"
                "h_factor : (m - p - q) * (m + p + q) = 5 * p * q\n"
                "⊢ p = q ∨ p = 3 ∧ q = 11 ∨ p = 11 ∧ q = 3")


def test_a_leaf_that_runs_out_of_heartbeats_is_retried_at_the_raised_budget():
    # Measured on rmo_2001_2 (v7.98, win h98): the divisor leaf closes the
    # live goal in a fresh theorem at 200000 heartbeats but needs 150000 of
    # them, so on a board whose earlier steps had spent some it failed with
    # "maximum number of heartbeats (200000)" five times; the raised budget
    # existed for model steps only, and no check ever ran at 400000.
    class HeavyLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            if "divisor_cases" in source and "vm_probe" not in source:
                self.sources.append(source)
                if "set_option maxHeartbeats 400000" in source:
                    return LeanCheck(True, [], False, False, 1)
                at = next(i for i, l in enumerate(source.split("\n"), start=1) if "divisor_cases" in l)
                return LeanCheck(False, [{"severity": "error", "pos": {"line": at}, "endPos": {"line": at},
                                          "data": "(deterministic) timeout at `whnf`, maximum number of "
                                                  "heartbeats (200000) has been reached"}], False, False, 1)
            if "vm_probe" not in source and not any(t in source for t in ("sorry", "skip", PROBE)):
                return LeanCheck(False, [{"severity": "error", "pos": {"line": 4}, "endPos": {"line": 4},
                                          "data": "linarith failed to find a contradiction"}], False, False, 1)
            check = await super().check_file(source, timeout_s)
            for m in check.messages:
                if str(m.get("data", "")).startswith("unsolved goals"):
                    m["data"] = "unsolved goals\n" + PRODUCT_GOAL
            return check

    lean, llm = HeavyLean(), ScriptLLM({"model-a": ["no"] * 6, "model-b": ["no"] * 6})
    agent = BoardAgent(Config(lines=("model-a", "model-b"), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=PRODUCT),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    assert any("set_option maxHeartbeats 400000" in s and "divisor_cases" in s for s in lean.sources)


def test_a_step_at_a_stated_goal_becomes_a_cell_checked_and_delivered_on_its_own():
    # Measured on rmo_2001_2 (v7.99, win h99): 6 checks ran out of heartbeats
    # at the raised 400000 because one theorem carried every step and the
    # leaf. A goal Lean can state is checked as its own declaration and
    # delivered as one, so each block has the whole budget to itself.
    lean, llm = CellLean(), ScriptLLM({"model-a": ["have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    # The root placeholder is the proof's own body: no cell there.
    assert "vm_cell_" not in result.solution and "-- cell" not in result.solution


def test_a_goal_under_a_have_is_checked_as_its_own_declaration_with_the_rest_stubbed():
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = CellLean(), ScriptLLM({
        "model-a": ["have outer : True := by\n  sorry\nexact outer",
                    "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=challenge),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    focused = [s for s in lean.sources if "theorem vm_cell_" in s and "have key : True := by trivial" in s]
    assert focused, "the step under `outer` was never checked as a cell"
    body = focused[0]
    # The cell carries the block; the theorem that holds it is a stub in that check.
    assert "theorem vm_cell_" in body and "(outer : P) : True := by" in body
    assert "theorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry" in body
    # Delivered: the cell before the theorem, linked from where it stood.
    text = result.solution
    assert text.index("theorem vm_cell_") < text.index("theorem demo")
    assert "    first | (exact vm_cell_" in text and "<;> assumption" in text and "-- cell" not in text


def test_a_leaf_that_only_fits_a_budget_of_its_own_passes_in_its_cell():
    # The fake refuses any declaration that holds both the earlier step and the
    # leaf (one budget); the leaf alone in a declaration of its own closes.
    PLAIN = "p q m : ℕ\nhp : Nat.Prime p\nhq : Nat.Prime q\n⊢ p = q ∨ p = 3 ∧ q = 11 ∨ p = 11 ∧ q = 3"

    class HeavyLean(CellLean):
        async def check_file(self, source, timeout_s=None):
            self.sources.append(source)
            probes = [i for i, l in enumerate(source.split("\n"), start=1)
                      if l.strip() in ("skip", PROBE, CELL_PROBE)]
            for body in re.findall(r"^theorem \w+[^\n]*:= by\n((?:[ \t]+[^\n]*\n?)*)", source, re.M):
                if "expensive" in body and "divisor_cases" in body:
                    at = next(i for i, l in enumerate(source.split("\n"), start=1) if "divisor_cases" in l)
                    return LeanCheck(False, [{"severity": "error", "pos": {"line": at}, "endPos": {"line": at},
                                              "data": "(deterministic) timeout at `whnf`, maximum number of "
                                                      "heartbeats (200000) has been reached"}], False, False, 1)
            if "divisor_cases" in source.split("-- end of techniques")[-1]:
                return LeanCheck(not probes, [{"severity": "error", "pos": {"line": at}, "endPos": {"line": at},
                                               "data": "No goals to be solved"} for at in probes], False, False, 1)
            if "vm_probe" not in source and not probes and "sorry" not in source:
                return LeanCheck(False, [{"severity": "error", "pos": {"line": 4}, "endPos": {"line": 4},
                                          "data": "linarith failed to find a contradiction"}], False, False, 1)
            check = await super().check_file(source, timeout_s)
            for m in check.messages:
                if str(m.get("data", "")).startswith("unsolved goals"):
                    m["data"] = "unsolved goals\n" + (PRODUCT_GOAL if "expensive" in source else PLAIN)
            return check

    lean, llm = HeavyLean(), ScriptLLM({"model-a": ["have expensive : True := by trivial"] + ["no"] * 6})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=PRODUCT),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    text = result.solution
    assert text.index("theorem vm_cell_") < text.index("theorem demo")
    checked = [s.split("-- end of techniques")[-1] for s in lean.sources
               if "divisor_cases" in s.split("-- end of techniques")[-1]]
    assert checked, "the divisor leaf was never checked"
    cell = checked[-1][checked[-1].index("theorem vm_cell_"):checked[-1].index("theorem demo")]
    assert "divisor_cases" in cell and "expensive" not in cell.split(":= by", 1)[1]
    assert "vm_cell_" in text


def test_an_identity_between_sums_ending_at_a_variable_gets_the_induction_leaf():
    # Measured on putnam_2020_a2's two-parameter generalisation (x98, v7.98):
    # given the statement, both models withdrew the Pascal step twice; the
    # mechanical step (peels as facts, rescaling, Pascal, omega) closes it in
    # the image in 0.5 s, and hockey-stick, Gauss and the geometric sum too.
    from submission.leaves import leaf_candidates
    from submission.techniques import uses_techniques, preamble
    goal = ("n m : ℕ\n⊢ ∑ j ∈ Finset.range (m + 1), 2 ^ (m - j) * (n + j).choose j = "
            "∑ i ∈ Finset.range (m + 1), (n + m + 1).choose i")
    assert leaf_candidates(goal)[0] == "set_option maxHeartbeats 400000 in (sum_induct m)"
    icc = "k : ℕ\n⊢ ∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * (k + j).choose j = 4 ^ k"
    assert any("sum_induct k" in c for c in leaf_candidates(icc))
    assert not any("sum_induct" in c for c in leaf_candidates("n : ℕ\nh : n < 5\n⊢ n ≤ 4"))
    assert not any("sum_induct" in c for c in leaf_candidates("x : ℝ\n⊢ ∑ i ∈ Finset.range (3 + 1), x = 4 * x"))
    assert uses_techniques(preamble() + "\ntheorem t (n : ℕ) : ∑ i ∈ Finset.range (n + 1), i * 2 = n * (n + 1) := by\n  sum_induct n\n")


def test_a_sum_identity_its_own_induction_misses_is_generalised_tabulated_fitted_and_posted():
    # Measured on putnam_2020_a2: 0 of 32 model proposals for a generalisation
    # were both true and new; the shape library fits the tabulated family
    # exactly (∑_{i≤k} C(n+k+1, i)) and the induction leaf proves that lemma.
    from math import comb
    PUTNAM = ("import Mathlib\n\ntheorem demo (k : ℕ) :\n    (∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * "
              "Nat.choose (k + j) j) = 4 ^ k := by\n  sorry\n")
    TARGET = "∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j = 4 ^ k"

    class ConjLean(CellLean):
        async def check_file(self, source, timeout_s=None):
            self.sources.append(source)
            if "def vm_table_" in source:
                fam = source.split(": ℕ := ", 1)[1].split("\n", 1)[0]
                if fam == "∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (n + j) j":
                    table = [[sum(2 ** (k - j) * comb(n + j, j) for j in range(k + 1)) for k in range(7)]
                             for n in range(6)]
                    return LeanCheck(True, [{"severity": "info", "pos": {"line": 2}, "data": str(table)}], False, False, 1)
                return LeanCheck(True, [], False, False, 1)
            if "decide ((" in source:
                ok = "Nat.choose (n + k + 1) i" in source and "Nat.choose (n + j) j" in source
                return LeanCheck(True, [{"severity": "info", "pos": {"line": 1}, "data": "true" if ok else "false"}], False, False, 1)
            probes = [i for i, l in enumerate(source.split("\n"), start=1) if l.strip() in ("skip", PROBE, CELL_PROBE)]
            body = source.split("-- end of techniques")[-1]
            lemma_at = body.find("theorem vm_conj_1")
            if "sum_induct" in body and lemma_at >= 0 and "sum_induct" in body[lemma_at:]:
                # The induction leaf closes the generalisation, not the theorem itself.
                return LeanCheck(not probes, [{"severity": "error", "pos": {"line": at}, "endPos": {"line": at},
                                               "data": "No goals to be solved"} for at in probes], False, False, 1)
            check = await super().check_file(source, timeout_s)
            for m in check.messages:
                if str(m.get("data", "")).startswith("unsolved goals") and "⊢ demo" in m["data"]:
                    m["data"] = m["data"].replace("⊢ demo", "⊢ " + TARGET).replace("unsolved goals\n", "unsolved goals\nk : ℕ\n")
                if str(m.get("data", "")).startswith("theorem") and ": demo :=" in m["data"]:
                    m["data"] = m["data"].replace(": demo :=", "(k : ℕ) : " + TARGET + " :=")
            return check

    lean, llm = ConjLean(), ScriptLLM({"model-a": ["no", "exact h_gen", "exact h_gen", "exact h_gen"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=PUTNAM),
                                     FakeServices(lean, llm)))
    events = result.metadata["events"]
    conj = [e for e in events if e.get("stage") == "conjecture"]
    assert conj and conj[0]["families"] == 3 and "∑ i ∈ Finset.range (k + 1), Nat.choose (n + k + 1) i" in conj[0]["fits"]
    assert any(e.get("stage") == "generalise" and e["lemma"] == "vm_conj_1" for e in events)
    posted = [s for s in lean.sources if "theorem vm_conj_1 (n k : ℕ)" in s and "have h_gen" in s]
    assert posted and ("have h_gen : ∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j = "
                       "∑ i ∈ Finset.range (k + 1), Nat.choose (2 * k + 1) i := by simpa only [← two_mul] "
                       "using vm_conj_1 k k") in posted[0]
    # The rewritten goal is put to Mathlib at once (Nat.sum_range_choose_halfway states it).
    assert any("apply?" in s and "rw [h_gen]" in s for s in lean.sources)
    assert result.metadata["solved_by"] == "board_loop"


def test_closing_the_last_goal_of_a_theorem_in_its_own_cell_is_not_read_as_unreachable():
    # Measured on putnam_2020_a2 (frame105): `exact Nat.sum_range_choose_halfway k`
    # closed the theorem's last goal in a fresh cell, but the theorem-level
    # `unsolved goals` report from before the edit was carried over and
    # `unreachable` refused the step; the run then spent 40 minutes re-proving it.
    # The first reply answers the shared-lemma question; `exact h` closes demo's
    # trailing goal (its own cell) and is wasted when demo_b is asked instead.
    lean, llm = CellLean(), ScriptLLM({
        "model-a": ["no", "have h : True := by trivial"] + ["exact h"] * 3 +
                   ["have key : True := by trivial\nexact key"] * 3})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=TWO),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    assert not any("nothing can get back to" in e.get("why", "") for e in result.metadata["events"])


def test_closing_a_cell_rechecks_its_parent_so_a_goal_without_a_placeholder_is_reopened():
    # Measured on rmo_2000_6 (frame108): a `case` block took its sibling's goal,
    # which Lean then reported on the theorem's header only; a step in a cell
    # closed the last placeholder, the stale header report was dropped, the
    # board read as finished and the comparator refused the file for sorryAx.
    # Now the parent is checked again, the goal gets a placeholder, and the run goes on.
    class HiddenGoalLean(CellLean):
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source, timeout_s)
            lines = source.split("\n")
            head = next((i for i, l in enumerate(lines, start=1) if l.startswith("theorem demo ")), None)
            full = head is not None and lines[head].strip() != "sorry"
            done = "exact hidden_done" in source
            messages = list(check.messages)
            if done:
                at = next(i for i, l in enumerate(lines, start=1) if "exact hidden_done" in l)
                messages = [m for m in messages
                            if not (str(m.get("data", "")).startswith("unsolved goals") and m["pos"]["line"] <= at <= m.get("endPos", m["pos"])["line"])]
                if at < len(lines) and lines[at].strip() in ("skip", PROBE, CELL_PROBE):
                    messages.append({"severity": "error", "pos": {"line": at + 1, "column": 2},
                                     "endPos": {"line": at + 1, "column": 4}, "data": "No goals to be solved"})
            elif full and "theorem vm_cell_" in source:
                # Lean reports a declaration's leftover goal on its `by`, spanning the proof.
                end = head
                while end < len(lines) and (lines[end].startswith(" ") or not lines[end].strip()):
                    end += 1
                messages.append({"severity": "error", "pos": {"line": head, "column": 2},
                                 "endPos": {"line": end, "column": 0},
                                 "data": "unsolved goals\ncase refine_2\n⊢ hidden"})
            errors = [m for m in messages if m["severity"] == "error"]
            return LeanCheck(not errors, messages, check.has_sorry, False, 1)

    lean, llm = HiddenGoalLean(), ScriptLLM({
        "model-a": ["have h : True := by trivial", "exact h"] + ["exact hidden_done"] * 4})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=ONE),
                                     FakeServices(lean, llm)))
    assert any(e.get("stage") == "reopen" for e in result.metadata["events"])
    assert result.metadata["solved_by"] == "board_loop"
    assert "exact hidden_done" in result.solution


def test_a_bound_on_a_product_from_a_numeral_dividing_a_product_of_its_powers_gets_the_radical_leaf():
    # Measured on rmo_2000_6 (frame117/119, 5 runs): `⊢ 10 ≤ a * b` under
    # `hdiv : 2000 ∣ a ^ 2 * b ^ 5` was the leaf every failing run died on
    # (6 model tries each); the pass took the same chain by hand: each prime
    # of 2000 to the bases, coprime product, Nat.le_of_dvd. 1.2 s in the image.
    from submission.leaves import leaf_candidates
    from submission.techniques import uses_techniques, preamble
    goal = ("a b : ℕ\nha : 0 < a\nhb : 0 < b\nhdiv : 2000 ∣ a ^ 2 * b ^ 5\n⊢ 10 ≤ a * b")
    got = [c for c in leaf_candidates(goal) if "prime_to_bases" in c]
    assert got and "prime_to_bases 2 hdiv" in got[0] and "prime_to_bases 5 hdiv" in got[0]
    assert "Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hp2 hp5" in got[0]
    assert "exact le_trans (by norm_num) (Nat.le_of_dvd (by positivity) hrad))" in got[0]
    # Typed numerals, the other order of the bases, a bare base, a ∣ target.
    typed = ("a b : ℕ\nha : (0 : ℕ) < a\nhdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)\n⊢ (10 : ℕ) ≤ b * a")
    assert any("prime_to_bases 5 hdiv" in c for c in leaf_candidates(typed))
    bare = "a b : ℕ\nh : 360 ∣ a * b ^ 3\n⊢ 30 ≤ a * b"
    assert any("prime_to_bases 3 h" in c for c in leaf_candidates(bare))
    named = "n a b : ℕ\nha : 0 < a\nhb : 0 < b\nhdiv : 2000 ∣ a ^ 2 * b ^ 5\nhn : n = a * b\n⊢ 10 ≤ n"
    assert any(c.startswith("set_option maxHeartbeats 400000 in (subst hn; have hp2 : 2 ∣ a * b") for c in leaf_candidates(named))
    dvd = "a b : ℕ\nh : 2000 ∣ a ^ 2 * b ^ 5\n⊢ 10 ∣ a * b"
    assert any("; exact hrad)" in c for c in leaf_candidates(dvd) if "prime_to_bases" in c)
    # Too weak (the radical is below the bound) or the wrong atoms: nothing.
    assert not any("prime_to_bases" in c for c in leaf_candidates("a b : ℕ\nh : 8 ∣ a ^ 2 * b\n⊢ 4 ≤ a * b"))
    assert not any("prime_to_bases" in c for c in leaf_candidates("a b c : ℕ\nh : 6 ∣ a * c\n⊢ 6 ≤ a * b"))
    assert uses_techniques(preamble() + "\ntheorem t (a : ℕ) (h : 6 ∣ a ^ 2) : 2 ∣ a := by\n  prime_to_bases 2 h\n")


def test_a_product_equation_over_the_integers_gets_a_divisor_leaf_that_linearises_each_case():
    # Measured on putnam_2018_a1 (frame117, 0/2): with `h_factor : (3a-2018)(3b-2018)
    # = 2018²` on the board the divisor leaf timed out at 400000 heartbeats; the
    # per-case `hx` was a hygienic name nothing could rewrite by, and omega chewed
    # on `h_eq : 2018 * (b + a) = a * b * 3`. Named hx, h_eq cleared: 3.6 s.
    from submission.leaves import leaf_candidates
    from submission.techniques import preamble
    goal = ("a b : ℤ\nh : 0 < a ∧ 0 < b\nh_eq : 2018 * (b + a) = a * b * 3\n"
            "h_factor : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2\n⊢ a = 673 ∨ a = 674")
    got = [c for c in leaf_candidates(goal) if "clear hm hdvd" in c]
    assert got and "clear hm hdvd h_eq;" in got[0] and "rw [hx] at h_factor; norm_num at h_factor <;> omega" in got[0]
    assert got[0].index("Dvd.intro _ h_factor") < got[0].index("clear hm")
    # Over ℕ the natAbs route is not taken, so no such block.
    nat = goal.replace("a b : ℤ", "a b : ℕ")
    assert not any("clear hm" in c for c in leaf_candidates(nat))
    assert "set_option hygiene false in\nmacro_rules\n  | `(tactic| divisor_cases $h for $x" in preamble()


def test_a_diophantine_cube_equation_asked_for_its_solution_gets_the_two_sided_squeeze_leaf():
    # Measured on rmo_2000_2 (frame116, 0/1 in 2615 s): the models took the
    # ℕ-subtraction identity `y³ - (x+2)³ = 2x(x-9)` and thrashed for 40 min.
    # Both sides of the squeeze, x substituted, the root squeezed: 4.2 s in the
    # image with no model asked.
    from submission.leaves import leaf_candidates
    goal = "x y : ℕ\nhx : 0 < x\nhy : 0 < y\nh : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8\n⊢ x = 9 ∧ y = 11"
    got = [c for c in leaf_candidates(goal) if "have hle : x ≤ 9" in c]
    assert got
    block = got[0]
    assert "pow_squeeze y 3 (x + 2) with hc)" in block and "nat_sub_exact; pow_squeeze y 3 (x + 1))" in block
    assert "have hv : x = 9 := (by omega); subst hv; norm_num at h ⊢; " in block and "pow_squeeze y 3 11" in block
    only_x = [c for c in leaf_candidates(goal.replace("⊢ x = 9 ∧ y = 11", "⊢ x = 9")) if "have hle : x ≤ 9" in c]
    assert only_x and only_x[0].rstrip().endswith("omega)") and "subst" not in only_x[0]
    # No subtraction on the right: no nat_sub_exact line.
    plain = "x y : ℕ\nh : y ^ 3 = x ^ 3 + 6 * x ^ 2 + 1\n⊢ x = 0 ∧ y = 1"
    got = [c for c in leaf_candidates(plain) if "have hle : x ≤ 0" in c]
    assert got and "nat_sub_exact" not in got[0] and "pow_squeeze y 3 (x + 2) with hc" in got[0]


def test_a_square_equal_to_a_symmetric_quadratic_in_two_variables_gets_the_difference_of_squares_leaf():
    # Measured on rmo_2001_2 (frame119 rmo12b, 0/1; 2 of 5 before): the pass had
    # `hfac : (m-p-q)(m+p+q) = 5pq` and `hdiv` on the board and the divisor leaf
    # closed the rest in 11 s; the failures wrote the 8-way disjunction instead
    # and withdrew it 4 times. The two steps from `hm` are mechanical.
    from submission.leaves import leaf_candidates
    goal = ("p q : ℕ\nhp : Nat.Prime p\nhq : Nat.Prime q\nm : ℕ\nhm : p ^ 2 + 7 * p * q + q ^ 2 = m ^ 2\n"
            "⊢ p = q ∨ p = 3 ∧ q = 11 ∨ p = 11 ∧ q = 3")
    got = [c for c in leaf_candidates(goal) if "have hfac" in c]
    assert got
    block = got[0]
    assert "have hle : p + q ≤ m := (by nlinarith [Nat.Prime.two_le hp, Nat.Prime.two_le hq])" in block
    assert "have hfac : (m - p - q) * (m + p + q) = 5 * p * q := (by obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle; subst hk" in block
    assert "have hdvd : m - p - q ∣ 5 * p * q := Dvd.intro _ hfac; prime_facts; divisor_cases hdvd <;> " in block
    assert "have hb_p : p ≤ 11" in block
    # The other way round, and k ≤ 2 gives nothing.
    flipped = goal.replace("hm : p ^ 2 + 7 * p * q + q ^ 2 = m ^ 2", "hm : m ^ 2 = p ^ 2 + 7 * p * q + q ^ 2")
    assert any("have hfac" in c for c in leaf_candidates(flipped))
    assert not any("have hfac" in c for c in leaf_candidates(goal.replace("7 * p * q", "2 * p * q")))


def test_a_block_sum_of_an_antitone_sequence_over_its_index_gets_the_block_bound_leaf():
    # Measured on rmo_2000_3 (0/2 on the cells build): the models state the block
    # bound ∑_{i∈[j²,(j+1)²)} x i / i ≤ 3 x(j²)/j and withdraw it after 4 tries; the
    # division inequality under monotonicity is the step neither lands. With the
    # lemma vm_sum_div_block the block closes in the image in 0.4 s.
    from submission.leaves import leaf_candidates
    from submission.techniques import preamble
    goal = ("x : ℕ → ℝ\nhpos : ∀ (n : ℕ), 0 < x n\nhmono : ∀ (n : ℕ), x n ≥ x (n + 1)\nj : ℕ\nhj : 1 ≤ j\n"
            "⊢ ∑ i ∈ Finset.Ico (j * j) ((j + 1) * (j + 1)), x i / ↑i ≤ 3 * (x (j * j) / ↑j)")
    got = [c for c in leaf_candidates(goal) if "vm_sum_div_block" in c]
    assert got
    block = got[0]
    assert "have hanti : Antitone x := antitone_nat_of_succ_le (fun n => hmono n)" in block
    assert "refine le_trans (vm_sum_div_block x hpos hanti (j * j) ((j + 1) * (j + 1)) (by first | positivity | omega | nlinarith)) ?_" in block
    assert "rw [Nat.cast_sub hle]; push_cast" in block and "have hj0 : (j : ℝ) ≠ 0 := (by exact_mod_cast (by omega : j ≠ 0))" in block
    assert "have hxp := hpos (j * j)" in block
    # Antitone already in scope: used by name; no monotonicity fact at all: no leaf.
    anti = goal.replace("hmono : ∀ (n : ℕ), x n ≥ x (n + 1)", "hanti : Antitone x")
    got = [c for c in leaf_candidates(anti) if "vm_sum_div_block" in c]
    assert got and "antitone_nat_of_succ_le" not in got[0] and "vm_sum_div_block x hpos hanti" in got[0]
    assert not any("vm_sum_div_block" in c for c in leaf_candidates(goal.replace("hmono : ∀ (n : ℕ), x n ≥ x (n + 1)\n", "")))
    assert "private theorem vm_sum_div_block" in preamble()


class EvalLean(BoardLean):
    """A file whose only probe is `#eval (7 ^ 2026 % 100)` prints 49."""

    async def check_file(self, source, timeout_s=None):
        if "#eval (7 ^ 2026 % 100)" in source:
            self.sources.append(source)
            return LeanCheck(True, [{"severity": "info", "pos": {"line": 3}, "endPos": {"line": 3},
                                     "data": "49"}], False, False, 1)
        return await super().check_file(source, timeout_s)


def test_an_answer_slot_equated_to_a_closed_term_is_evaluated_by_the_harness_not_asked():
    # Measured on p06 (frame124 reg): gpt-oss wrote `#eval (Nat.modPow 7 2026 100)`
    # three times (no such name), qwen narrated without an `#eval`, the slot
    # stayed `sorry` and 1258 s went into `49 = sorry`. The statement itself
    # says what to evaluate: `7 ^ 2026 % 100 = p06_answer`, no binders.
    from submission.framework import statement_probes
    challenge = ("import Mathlib\n\n/-- doc -/\nabbrev p06_answer : ℕ := sorry\n\n"
                 "theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by\n  sorry\n")
    assert statement_probes(challenge, ["p06_answer"]) == ["#eval (7 ^ 2026 % 100)"]
    # Binders, or a side that is not closed, give nothing.
    assert statement_probes(challenge.replace("theorem p06_pow_mod :", "theorem p06_pow_mod (n : ℕ) :"),
                            ["p06_answer"]) == []
    assert statement_probes("abbrev a : ℕ := sorry\ntheorem t : a = ∑ i ∈ Finset.range 3, f i := by\n  sorry\n",
                            ["a"]) == []
    assert statement_probes("abbrev a : ℕ := sorry\ntheorem t : IsLeast {n | n > 3} a := by\n  sorry\n", ["a"]) == []
    step = "have key : True := by trivial\nexact key"
    lean, llm = EvalLean(), ScriptLLM({"model-a": [step] * 3, "model-b": [step] * 3})
    agent = BoardAgent(Config(lines=("model-a", "model-b"), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="p06", description="compute", challenge=challenge),
                                     FakeServices(lean, llm)))
    assert "abbrev p06_answer : ℕ := 49" in result.solution
    probes = [e for e in result.metadata["events"] if e.get("stage") == "probe"]
    assert probes and probes[0]["by"] == "harness" and probes[0]["printed"] == ["49"]
    assert not any("#eval" in p for _, p in llm.calls)


def test_a_leaf_is_checked_at_the_cap_timeout_and_its_own_cost_is_not_a_slow_step():
    # Measured on rmo_2001_2 (frame123, 0/2 with the difference-of-squares leaf
    # on board): the leaf takes 12 s in an idle image and 50 s on a loaded host;
    # judged as a model step it hit the 30 s check timeout (one candidate tried,
    # then break) and the 10 s slow-step delta. A leaf is one cell, paid once.
    from submission.board.probes import CHECK_TIMEOUT_CAP_S

    class SlowLeafLean(BoardLean):
        """The theorem's goal carries `hb : x ≤ 3`; every check with the leaf
        (or with the model's `omega`) closes it, but takes 15 s."""
        def __init__(self):
            super().__init__()
            self.timeouts: list[tuple[str, int | None]] = []
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source)
            if "theorem demo" in source and ("interval_cases x" in source or "\n  omega" in source):
                self.timeouts.append(("leaf" if "interval_cases x" in source else "step", timeout_s))
                return LeanCheck(True, [], False, False, 15_000)
            msgs = [dict(m, data=m["data"].replace("⊢ demo", "hb : x ≤ 3\n⊢ x = 2"))
                    if "⊢ demo" in str(m.get("data")) else m for m in check.messages]
            return LeanCheck(check.accepted, msgs, check.has_sorry, False, 1)

    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hb : x ≤ 3) : x = 2 := by\n  sorry\n"
    lean, llm = SlowLeafLean(), ScriptLLM({"model-a": ["omega"] * 3})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=challenge),
                                     FakeServices(lean, llm)))
    leaf = [e for e in result.metadata["events"] if e.get("kind") == "leaf"]
    assert leaf and leaf[0]["accepted"] and "interval_cases x" in result.solution
    assert lean.timeouts and lean.timeouts[0] == ("leaf", CHECK_TIMEOUT_CAP_S)
    assert not any(e.get("stage") == "slow" for e in result.metadata["events"])
    # The same 15 s from a model step is still refused as slow.
    lean2, llm2 = SlowLeafLean(), ScriptLLM({"model-a": ["omega"] * 3})
    lean2.no_leaf = True
    from submission import board_agent as ba
    from submission.run import ladder
    saved = ladder.leaf_candidates
    ladder.leaf_candidates = lambda text: []
    try:
        result2 = asyncio.run(BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0)).solve(
            Problem(id="demo", description="p", challenge=challenge), FakeServices(lean2, llm2)))
    finally:
        ladder.leaf_candidates = saved
    assert any(e.get("stage") == "slow" for e in result2.metadata["events"])
    assert lean2.timeouts and lean2.timeouts[0][1] < CHECK_TIMEOUT_CAP_S


class RecallLean(CellLean):
    """CellLean whose stated goals name each hypothesis once, so a claim under
    a shadowing `have` of the same name states the same theorem."""

    async def check_file(self, source, timeout_s=None):
        check = await super().check_file(source, timeout_s)
        out = []
        for m in check.messages:
            data = str(m.get("data", ""))
            if ".extracted_1" in data:
                seen: set[str] = set()
                parts = [tok for tok in re.findall(r"\(\w+ : P\)|\S+", data)
                         if not (tok.startswith("(") and tok in seen) and not seen.add(tok)]
                m = dict(m, data=" ".join(parts))
            out.append(m)
        return LeanCheck(check.accepted, out, check.has_sorry, check.timed_out, check.duration_ms)


def test_a_goal_already_proved_in_a_closed_cell_is_closed_again_by_recall_not_by_a_model():
    # Measured on rmo_2001_2 (frame123): the divisor leaf closed the final goal
    # in its cell at 67 s, then the enclosing have was withdrawn after four
    # failures and the goal came back as new. A closed cell is a proof of a
    # stated theorem; the same statement is closed by that block, no model asked.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean = RecallLean()
    llm = ScriptLLM({"model-a": ["have a1 : True := by\n  exfalso\n  sorry\nhave a1 : True := by\n  exfalso\n  sorry\nexact a1",
                                 "exact a1"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=challenge),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    assert any(e.get("stage") == "proven" and e["stmt"].endswith(": False") for e in result.metadata["events"])
    recalls = [e for e in result.metadata["events"] if e.get("kind") == "recall"]
    assert recalls and recalls[0]["goal"].endswith("⊢ False")
    # Two scripted replies; the second `False` goal never reached a model.
    asked = [p for _, p in llm.calls if "What Lean reports as open" in p]
    assert len(asked) == 2


def test_a_block_that_does_not_parse_gets_the_parse_error_alone_and_no_prefix_hunt():
    # Measured on rmo_2000_6 (frame120 rmo6b): one step with an unclosed bracket
    # (`unexpected token 'have'; expected '}'`) desynchronised the parser, every
    # later line of the file reported `Unknown identifier`, and prefixes and
    # retries of the same block were checked 82 times, 1151 such messages.

    class ParseLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source, timeout_s)
            lines = source.split("\n")
            at = next((i for i, l in enumerate(lines, start=1) if l.strip().startswith("refine ⟨oops")), None)
            if at is None:
                return check
            msgs = [{"severity": "error", "pos": {"line": at + 1, "column": 4}, "endPos": {"line": at + 1},
                     "data": "unexpected token 'have'; expected '}'"}]
            msgs += [{"severity": "error", "pos": {"line": k, "column": 4}, "endPos": {"line": k},
                      "data": "Unknown identifier `a`"} for k in range(max(1, at - 3), at)]
            return LeanCheck(False, msgs + check.messages, check.has_sorry, False, 1)

    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    bad = "have h1 : True := by trivial\nrefine ⟨oops, {\nhave h2 : True := by trivial\nexact h2"
    lean, llm = ParseLean(), ScriptLLM({"model-a": [bad, "have key : True := by trivial\nexact key"]})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=challenge),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    checked = [s for s in lean.sources if "refine ⟨oops" in s]
    assert len(checked) <= 2, f"{len(checked)} checks of a block that does not parse"
    rejected = [e for e in steps(result) if not e["accepted"]]
    assert rejected and "unexpected token" in rejected[0]["why"] and "Unknown identifier" not in rejected[0]["why"]
    assert not any(e.get("kind") in ("prefix", "search-retry") for e in result.metadata["events"])


def test_a_step_that_closes_its_goal_is_not_refused_for_its_own_check_time():
    # Measured on rmo_2001_2 (frame125 rmo12b, 0/1): seven steps that closed
    # the reverse direction's goal were refused as slow at 12-13 s (from 0.2 s).
    # A closing step is never re-elaborated by a later focused check; only the
    # comparator's cold compile pays it, which the absolute cap guards.

    class SlowCloseLean(BoardLean):
        async def check_file(self, source, timeout_s=None):
            check = await super().check_file(source, timeout_s)
            if "theorem demo" in source and "exact key" in source:
                return LeanCheck(check.accepted, check.messages, check.has_sorry, False, 15_000)
            return check

    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean, llm = SlowCloseLean(), ScriptLLM({"model-a": ["have key : True := by trivial\nexact key"] * 3})
    agent = BoardAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=challenge),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    assert not any(e.get("stage") == "slow" for e in result.metadata["events"])
    from submission.sweep import COCKTAIL
    assert "subst_vars <;> ring" in COCKTAIL and "subst_vars <;> nlinarith" in COCKTAIL


def test_a_goal_a_model_has_repeated_on_is_not_offered_to_it_again_until_the_board_changes():
    # Measured on rmo_2000_6 (frame128): qwen resubmitted the same rejected
    # block 1190 times (runs of 125 in a row), 1393 model calls in the run,
    # most of them repeats the detector caught after the call was paid for.
    challenge = "import Mathlib\n\ntheorem demo (x : ℕ) (hx : x < 2) : True := by\n  sorry\n"
    lean = BoardLean()
    llm = ScriptLLM({"model-a": ["exact gone"] * 40,
                     "model-b": ["have key : True := by trivial\nexact key"]},
                    delay={"model-b": 2.0})
    agent = BoardAgent(Config(lines=("model-a", "model-b"), budget_usd=1.0, time_limit_s=600.0, audit=False))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p", challenge=challenge),
                                     FakeServices(lean, llm)))
    assert result.metadata["solved_by"] == "board_loop"
    repeats = [e for e in result.metadata["events"] if e.get("kind") == "repeat"]
    assert len(repeats) <= 1, f"{len(repeats)} repeats"
    assert sum(1 for m, _ in llm.calls if m == "model-a") <= 3


def test_leaf_reads_past_a_set_forall_and_a_conjunction_hypothesis():
    # rmo_2000_6 (frame129, 12bf666): the radical leaf was accepted 4 times on
    # `⊢ 10 ≤ a * b` and the run still failed on these two outer shapes.
    from submission.leaves import leaf_candidates
    outer = "⊢ ∀ n ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b}, 10 ≤ n"
    got = leaf_candidates(outer)
    assert got and got[0].startswith("set_option maxHeartbeats 400000 in (intro n vm_hn; obtain ⟨a, b, vm_c0, vm_c1, vm_c2, vm_c3⟩ := vm_hn; subst vm_c3; ")
    assert "prime_to_bases 2 vm_c2" in got[0] and "Nat.le_of_dvd" in got[0]
    lower = "⊢ 10 ∈ lowerBounds {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b}"
    assert any("prime_to_bases 5" in c for c in leaf_candidates(lower))
    conj = "n a b : ℕ\nha : 0 < a\nhb : 0 < b\nhdiv : 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b\n⊢ 10 ≤ n"
    got = leaf_candidates(conj)
    assert got[0].startswith("set_option maxHeartbeats 400000 in (obtain ⟨vm_hdiv0, vm_hdiv1⟩ := hdiv; subst vm_hdiv1; ")
    # A bound variable named differently from the set's own is renamed.
    assert leaf_candidates(outer.replace("∀ n ∈", "∀ m ∈").replace(", 10 ≤ n", ", 10 ≤ m"))[0].startswith(
        "set_option maxHeartbeats 400000 in (intro m vm_hn;")


def test_an_inaccessible_hypothesis_becomes_a_named_binder_of_the_cell():
    # rmo_2000_6 (frame130): `a✝ : 10 ∈ S` came back as `10 ∈ S → ∀ n ∈ S, 10 ≤ n`,
    # the link passed no argument and a leaf's `intro n` took the premise.
    from submission.board.probes import read_board
    from submission.cells import link
    S = "{n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b}"
    St = "{n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b}"
    text = f"import Mathlib\n\ntheorem demo : ∀ n ∈ {S}, 10 ≤ n := by\n  sorry\n"
    messages = [
        {"severity": "error", "pos": {"line": 3, "column": 40}, "endPos": {"line": 4, "column": 7},
         "data": f"unsolved goals\na✝ : 10 ∈ {S}\n⊢ ∀ n ∈ {S}, 10 ≤ n"},
        {"severity": "info", "pos": {"line": 4, "column": 2}, "endPos": {"line": 4, "column": 14},
         "data": f"theorem demo.extracted_1 : (10 : ℕ) ∈ {St} → ∀ n ∈ {St}, (10 : ℕ) ≤ n := sorry"},
    ]
    goal = read_board(text, messages, False).goals[0]
    assert goal.stmt == f"(vm_p1 : (10 : ℕ) ∈ {St}) : ∀ n ∈ {St}, (10 : ℕ) ≤ n"
    assert link(7, goal.stmt).startswith("first | (exact vm_cell_7 ‹_›)")
    # A goal that is itself an implication keeps its arrow.
    messages[0]["data"] = "unsolved goals\n⊢ 0 < x → 0 < x + 1"
    messages[1]["data"] = "theorem demo.extracted_1 (x : ℕ) : (0 : ℕ) < x → (0 : ℕ) < x + (1 : ℕ) := sorry"
    assert read_board(text, messages, False).goals[0].stmt == "(x : ℕ) : (0 : ℕ) < x → (0 : ℕ) < x + (1 : ℕ)"


def test_vm_leaves_off_disables_the_leaf_sweep(monkeypatch):
    from submission.config import Config
    monkeypatch.setenv("VM_LEAVES", "off")
    assert Config.from_env().leaves is False
    monkeypatch.delenv("VM_LEAVES")
    assert Config.from_env().leaves is True


def test_a_sum_bounded_through_its_subsequence_at_the_squares_is_a_leaf():
    # The goal is quoted from a run (frame133, rmo_2000_3): `open Finset` in the
    # challenge makes Lean print `Ico`, and the top goal still carries its `∀ k`.
    from submission.leaves import leaf_candidates
    goal = ("x : ℕ → ℝ\nhpos : ∀ (n : ℕ), 0 < x n\nhmono : ∀ (n : ℕ), x n ≥ x (n + 1)\n"
            "hsq : ∀ (N : ℕ), ∑ i ∈ Ico 1 (N + 1), x (i * i) / ↑i ≤ 1\n"
            "⊢ ∀ (k : ℕ), ∑ i ∈ Ico 1 (k + 1), x i / ↑i ≤ 3")
    got = next((c for c in leaf_candidates(goal) if "ico_blocks k" in c), "")
    assert got.startswith("set_option maxHeartbeats 400000 in (intro k; ")
    assert "vm_sum_div_block x hpos vm_anti" in got and "hsq k" in got
    assert got.index("vm_split") < got.index("vm_block") < got.index("linarith")
    # The same after the binder is introduced, and with `Finset.` spelled out.
    inner = goal.replace("⊢ ∀ (k : ℕ), ", "k : ℕ\n⊢ ").replace("Ico", "Finset.Ico")
    assert any("ico_blocks k" in c for c in leaf_candidates(inner))
    # The constant has to cover three times the hypothesis's bound.
    assert not any("ico_blocks" in c for c in leaf_candidates(goal.replace("≤ 3", "≤ 2")))
    # Without the monotonicity there is no Antitone to hand the lemma.
    assert not any("ico_blocks" in c for c in
                   leaf_candidates(goal.replace("hmono : ∀ (n : ℕ), x n ≥ x (n + 1)\n", "")))


def test_a_quantified_goal_with_no_candidate_of_its_own_is_introduced():
    # Grouped binders too: Lean prints `∀ (a b : ℕ), …` for one binder group.
    from submission.leaves import leaf_candidates
    goal = ("x : ℕ → ℝ\nhpos : ∀ (n : ℕ), 0 < x n\nhmono : ∀ (n : ℕ), x n ≥ x (n + 1)\n"
            "hsq : ∀ (N : ℕ), ∑ i ∈ Ico 1 (N + 1), x (i * i) / ↑i ≤ 1\n"
            "⊢ ∀ (j k : ℕ), ∑ i ∈ Ico 1 (k + 1), x i / ↑i ≤ 3")
    got = next((c for c in leaf_candidates(goal) if "ico_blocks k" in c), "")
    assert got.startswith("set_option maxHeartbeats 400000 in (intro j k; ")


def test_an_is_least_over_a_product_is_a_leaf():
    # Both goals are quoted from a run (frame134, rmo_2000_6).
    from submission.leaves import leaf_candidates
    one = ("⊢ IsLeast {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10")
    got = next((c for c in leaf_candidates(one) if "prime_to_bases" in c), "")
    # The witness of `n = a * b` at a literal is one of its factor pairs.
    assert "exact ⟨1, 10, by norm_num⟩" in got and "exact ⟨2, 5, by norm_num⟩" in got
    assert "Nat.le_of_dvd" in got and "vm_c2" in got
    # A radical below the claimed least element carries no bound.
    assert not any("prime_to_bases" in c for c in leaf_candidates(one.replace("} 10", "} 11")))


def test_a_conjunction_of_two_leaf_goals_is_one_block():
    from submission.leaves import leaf_candidates
    both = ("⊢ IsLeast {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10 ∧ "
            "IsLeast {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10")
    got = leaf_candidates(both)
    assert len(got) == 1
    # `And.intro`, since `IsLeast` is itself a conjunction and swallows `⟨_, _⟩`.
    assert "refine And.intro (by " in got[0]
    assert got[0].count("prime_to_bases 5") == 2


def test_a_pair_of_reciprocals_against_a_listed_solution_set_is_a_leaf():
    # The goal is quoted from a run (frame134, putnam_2018_a1), wrapped as Lean
    # printed it.
    from submission.leaves import leaf_candidates
    goal = ("a b : ℤ\nh : 0 < a ∧ 0 < b\n"
            "⊢ 1 / ↑a + 1 / ↑b = 3 / 2018 ↔\n"
            "    (a, b) ∈ {(673, 1358114), (674, 340033), (1009, 2018), (2018, 1009),"
            " (340033, 674), (1358114, 673)}")
    got = next((c for c in leaf_candidates(goal) if "Iff.intro" in c), "")
    assert "(3 * a - 2018) * (3 * b - 2018) = (2018 : ℤ) ^ 2" in got
    assert "divisor_cases vm_dvd" in got
    # One `rfl` pair per listed solution, and the commas inside a pair do not count.
    assert got.count("⟨rfl, rfl⟩") == 6
    # Every `have` hands its proof a parenthesised `by`, or the block is swallowed.
    assert ":= by " not in got
