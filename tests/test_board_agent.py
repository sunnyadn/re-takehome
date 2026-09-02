import asyncio
import re
import time

from re_harness import Problem
from re_harness.lean import LeanCheck
from submission.agent import Config
from submission.board_agent import (
    Board, BoardAgent, Goal, interpret, read_board, render_all,
)
from tests.test_framework_loop import FakeServices, said

ONE = "import Mathlib\n\ntheorem demo : True := by\n  sorry\n"
TWO = ("import Mathlib\n\ntheorem demo : True := by\n  sorry\n\n"
       "theorem demo_b : True := by\n  sorry\n")
HEAD = re.compile(r"^\s*(?:theorem|lemma)\s+(\w+)")


class BoardLean:
    """Every `skip` reports its own goal, whose hypotheses are the `have`s above
    it in the same declaration. `exact key` closes when `key` is in scope."""

    def __init__(self):
        self.sources: list[str] = []

    async def check_file(self, source, timeout_s=None):
        self.sources.append(source)
        if "vm_probe" in source:
            return LeanCheck(True, [], False, False, 1)
        messages, decl, haves = [], "", []
        for i, line in enumerate(source.split("\n"), start=1):
            head = HEAD.match(line)
            if head:
                decl, haves = head.group(1), []
                continue
            body = line.strip()
            if body.startswith("have "):
                haves.append(body.split()[1])
            if body.startswith(("first", "exact?", "linarith")):
                messages.append({"severity": "error", "pos": {"line": i - 1},
                                 "endPos": {"line": i - 1},
                                 "data": "linarith failed to find a contradiction"})
            if body == "skip":
                closed = any(f"exact {h}" in source.split("\n")[j]
                             for j in range(i - 2, -1, -1)
                             if HEAD.match(source.split("\n")[j]) is None
                             for h in haves) if haves else False
                if closed:
                    continue
                hyps = "".join(f"{h} : P\n" for h in haves)
                messages.append({"severity": "error", "pos": {"line": i - 2},
                                 "endPos": {"line": i - 1},
                                 "data": f"unsolved goals\n{hyps}⊢ {decl}"})
        errors = [m for m in messages if m["severity"] == "error"]
        return LeanCheck(not errors, messages, "sorry" in source, False, 1)


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
        if self.delay.get(model):
            await asyncio.sleep(self.delay[model])
        if "competition mathematician" in messages[0]["content"]:
            return said("Take the obvious route.", 0.001)
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


def steps(result):
    return [e for e in result.metadata["events"] if e.get("kind") == "step"]


def test_every_placeholder_is_rendered_as_skip_at_once():
    assert render_all(TWO).count("skip") == 2 and "sorry" not in render_all(TWO)


def test_the_board_reads_one_goal_per_placeholder_with_its_own_context():
    text = ("import Mathlib\n\ntheorem demo : True := by\n  have k : True := by\n"
            "    sorry\n  sorry\n\ntheorem demo_b : True := by\n  sorry\n")
    check = asyncio.run(BoardLean().check_file(render_all(text)))
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
        "model-a": ["no", "no", "theorem demo_b : True := by trivial",
                    "have key : True := by trivial", "exact key"],
    }, lines=("model-a",))
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
    from submission.board_agent import view
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
        "model-a": ["linarith", "exact?", skeleton, "exact key", "exact key", "exact key"],
    }, lines=("model-a",))
    asked = [p for m, p in llm.calls if "Write the plan as a skeleton" in p]
    assert len(asked) == 1 and "mathematician was asked" in asked[0]
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
    result, lean, llm, _ = run(ONE, {
        "model-a": ["have key : P := by\n  sorry\nexact key",
                    "linarith", "linarith", "linarith", "linarith",
                    "have other : True := by trivial", "exact other"],
    }, lines=("model-a",))
    events = result.metadata["events"]
    assert any(e.get("kind") == "withdraw" and "key : P" in e.get("have", "") for e in events)
    assert any("withdrawn" in p for _, p in llm.calls)
    assert "have key : P" not in result.solution
    assert result.metadata["accepted_by_repl"] is True
