"""The loop's control: accept, discard, settle, take turns, stop on budget."""

from __future__ import annotations

import asyncio

from re_harness import LLMCallError, Problem
from re_harness.lean import LeanCheck
from submission.agent import Config
from submission.framework_agent import FrameworkAgent

CHALLENGE = "import Mathlib\n\ntheorem demo : True := by\n  sorry\n"


def skip_line(source: str) -> int:
    for i, line in enumerate(source.split("\n"), start=1):
        if line.strip() == "skip":
            return i
    return 0


def unsolved(line: int, goal: str = "True") -> LeanCheck:
    return LeanCheck(accepted=False, has_sorry=True, timed_out=False, duration_ms=1,
                     messages=[{"severity": "error", "pos": {"line": line},
                                "data": f"unsolved goals\n⊢ {goal}"}])


class FakeLean:
    """`exact key` closes the goal; the cocktail never does. Records every check."""

    def __init__(self):
        self.sources: list[str] = []

    async def check_file(self, source, timeout_s=None):
        self.sources.append(source)
        line = skip_line(source)
        if "vm_probe" in source:
            return LeanCheck(True, [], False, False, 1)
        if "exact key" in source:
            # A name deleted from the file is a name out of scope, which is what
            # makes the finish pass's deletion test sound.
            if "have key" not in source:
                return LeanCheck(False, [{"severity": "error", "pos": {"line": line or 1},
                                          "data": "unknown identifier 'key'"}], True, False, 1)
            if line:
                # Measured on the graded image: a `skip` with no goals left is a
                # linter warning and the file is accepted, not an error.
                return LeanCheck(True, [{"severity": "warning", "pos": {"line": line},
                                         "data": "'skip' tactic does nothing"}],
                                 False, False, 1)
            return LeanCheck(True, [], False, False, 1)
        if "first" in source or "exact?" in source:
            return LeanCheck(False, [{"severity": "error", "pos": {"line": line or 1},
                                      "data": "linarith failed to find a contradiction"}],
                             True, False, 1)
        return unsolved(line)


def wrote(llm):
    """The turns that asked for Lean, which is what most tests are about."""

    return [(m, text) for m, text, planning in llm.calls if not planning]


PLAN = "Take the obvious route: state the fact and close it."


def said(content: str, cost: float, finish: str = "stop"):
    return type("R", (), {"content": content, "usage": {"cost": cost},
                          "finish_reason": finish})()


class FakeLLM:
    """The script drives the writer; the planner answers with a canned plan."""

    def __init__(self, replies):
        self.replies, self.calls = list(replies), []

    async def complete(self, *, model, messages, **kwargs):
        planning = "competition mathematician" in messages[0]["content"]
        self.calls.append((model, messages[-1]["content"], planning))
        if planning:
            return said(PLAN, 0.001)
        reply = self.replies.pop(0) if self.replies else "have junk : True := by trivial"
        # A reply the provider cut is marked, so the loop can tell it from a step.
        if reply == "__cut__":
            return said("have half : True := by", 0.01, "length")
        return said(reply, 0.01)


class FakeServices:
    def __init__(self, lean, llm):
        self.lean, self.llm, self.checkpoints = lean, llm, []

    def checkpoint(self, source, metadata=None):
        self.checkpoints.append(source)


def run(replies, budget=1.0, lines=("model-a", "model-b")):
    lean, llm = FakeLean(), FakeLLM(replies)
    services = FakeServices(lean, llm)
    cfg = Config(lines=lines, budget_usd=budget, time_limit_s=600.0)
    agent = FrameworkAgent(cfg)
    problem = Problem(id="demo", description="prove it", challenge=CHALLENGE)
    result = asyncio.run(agent.solve(problem, services))
    return result, lean, llm, services


def test_a_step_that_compiles_stays_and_a_closing_step_finishes_the_proof():
    result, lean, llm, services = run(["have key : True := by trivial", "exact key"])
    assert result.metadata["accepted_by_repl"] is True
    assert "have key : True := by trivial" in result.solution
    assert "exact key" in result.solution
    assert "sorry" not in result.solution and "skip" not in result.solution
    assert services.checkpoints and services.checkpoints[-1] == result.solution


def test_the_closers_are_tried_before_any_model_is_asked():
    _, lean, llm, _ = run(["have key : True := by trivial", "exact key"])
    swept = next(i for i, s in enumerate(lean.sources) if "first" in s and "vm_probe" not in s)
    assert swept < len(lean.sources)
    assert len(wrote(llm)) == 2


def test_a_rejected_step_is_removed_from_the_file():
    replies = ["have bad : True := by first | (rfl; done)",
               "have worse : True := by exact?",
               "have key : True := by trivial", "exact key"]
    result, _, llm, _ = run(replies)
    # One model writes until Lean rejects it twice; the swap is covered elsewhere.
    assert [m for m, _ in wrote(llm)][:2] == ["model-a", "model-a"]
    assert "bad" not in result.solution and "worse" not in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_lean_s_own_words_are_carried_into_the_next_attempt():
    replies = ["have bad : True := by first | (rfl; done)",
               "have key : True := by trivial", "exact key"]
    _, _, llm, _ = run(replies)
    assert "linarith failed" in wrote(llm)[1][1]
    assert "Every closer before nlinarith" in wrote(llm)[1][1]
    # The closers are the harness's attempt, not the model's; saying otherwise
    # asks the model to correct a step it never wrote.
    assert "Your last step" not in wrote(llm)[0][1]
    assert "A search attempt on this goal was rejected" in wrote(llm)[0][1]
    assert "Your last step was rejected" in wrote(llm)[1][1]
    assert wrote(llm)[1][0] == wrote(llm)[0][0]


def test_the_loop_stops_asking_once_the_budget_headroom_is_gone():
    result, _, llm, _ = run(["have junk : True := by trivial"] * 20, budget=0.02)
    assert len(wrote(llm)) <= 2
    assert result.metadata["accepted_by_repl"] is False
    stopped = [e for e in result.metadata["events"] if e.get("note") == "budget headroom"]
    assert stopped


class AxiomLean(FakeLean):
    """Lean accepts the file, but `#print axioms` names one off the allowlist."""

    async def check_file(self, source, timeout_s=None):
        if "#print axioms" in source:
            return LeanCheck(True, [{"severity": "info", "data":
                "'demo' depends on axioms: [propext, demo._native.native_decide.ax_1]"}],
                False, False, 1)
        return await super().check_file(source)


def test_an_axiom_off_the_allowlist_is_not_offered_as_a_win():
    lean, llm = AxiomLean(), FakeLLM(["have key : True := by trivial", "exact key"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="d", challenge=CHALLENGE), services))
    assert result.metadata["accepted_by_repl"] is False
    verify = [e for e in result.metadata["events"] if e.get("stage") == "verify"]
    assert verify and verify[0]["faults"]


class SlowLean(FakeLean):
    """`have key` only fits inside the elaboration budget once it is raised."""

    async def check_file(self, source, timeout_s=None):
        if "have key" in source and "maxHeartbeats" not in source:
            return LeanCheck(False, [{"severity": "error", "pos": {"line": skip_line(source)},
                                      "data": "(deterministic) timeout at `whnf`, maximum "
                                              "number of heartbeats (200000)"}],
                             True, False, 1)
        return await super().check_file(source)


def test_a_step_that_only_ran_out_of_budget_is_given_the_budget():
    lean, llm = SlowLean(), FakeLLM(["have key : True := by trivial", "exact key"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="d", challenge=CHALLENGE), services))
    assert "set_option maxHeartbeats 400000" in result.solution
    assert "have key" in result.solution
    assert result.metadata["accepted_by_repl"] is True
    # The step was not blamed for it: the model was never asked to replace it.
    assert len(wrote(llm)) == 2


class ProbeLean(FakeLean):
    async def check_file(self, source, timeout_s=None):
        if "#eval" in source:
            return LeanCheck(False, [{"severity": "info", "data": "77"}], True, False, 1)
        return await super().check_file(source)


def test_a_probe_goes_above_the_theorem_and_comes_back_as_a_number():
    lean = ProbeLean()
    llm = FakeLLM(["#eval (77 : ℕ)", "have key : True := by trivial", "exact key"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="d", challenge=CHALLENGE), services))
    # The probe is read from its own check and left out of the proof.
    assert "#eval" not in result.solution
    assert "The probe you asked for printed:\n77" in wrote(llm)[1][1]
    assert result.metadata["accepted_by_repl"] is True


def test_a_fact_the_finished_proof_does_not_use_is_deleted(monkeypatch):
    import submission.framework_agent as fa_mod

    # The gate is a size, not a rule: below it §4 says leave the file alone.
    monkeypatch.setattr(fa_mod, "TIDY_ABOVE_BYTES", 0)
    replies = ["have spare : True := by trivial", "have key : True := by trivial",
               "exact key"]
    result, lean, _, _ = run(replies)
    assert result.metadata["accepted_by_repl"] is True
    # `spare` is never named again, and the file still checks without it.
    assert "spare" not in result.solution and "have key" in result.solution


ANSWER_CHALLENGE = ("import Mathlib\n\nabbrev p_answer : ℕ := sorry\n\n"
                    "theorem demo : p_answer = 77 := by\n  sorry\n")


class AnswerLean(FakeLean):
    """The first probe prints nothing usable; the second prints the number."""

    def __init__(self):
        super().__init__()
        self.probes = 0

    async def check_file(self, source, timeout_s=None):
        if "#eval" in source:
            self.probes += 1
            data = "unable to evaluate" if self.probes == 1 else "77"
            return LeanCheck(False, [{"severity": "info", "data": data}], True, False, 1)
        return await super().check_file(source)


def test_an_unfilled_answer_slot_is_noticed_and_asked_for_again():
    lean, llm = AnswerLean(), FakeLLM(["#eval 1 + 1", "#eval 70 + 7",
                                       "have key : True := by trivial", "exact key"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="d", challenge=ANSWER_CHALLENGE), services))
    probes = [e for e in result.metadata["events"] if e.get("stage") == "probe"]
    assert probes[0]["unfilled"] == ["p_answer"] and probes[1]["unfilled"] == []
    assert "abbrev p_answer : ℕ := 77" in result.solution
    assert "sorry" not in result.solution


def test_facts_that_never_move_the_goal_are_rolled_back():
    junk = [f"have j{i} : True := by trivial" for i in range(8)]
    result, _, llm, _ = run(junk + ["exact key"], lines=("model-a", "model-b"))
    reverts = [e for e in result.metadata["events"] if e.get("stage") == "revert"]
    assert reverts and reverts[0]["dropped"] == 6
    # The model is told what was removed, and the other one gets the next turn.
    told = [c for _, c, _ in llm.calls if "left the goal standing" in c]
    assert told and "j0 : True" in told[0]


def test_a_model_that_never_gives_a_usable_step_does_not_spin():
    result, lean, llm, _ = run(["skip"] * 200)
    stuck = [e for e in result.metadata["events"] if e.get("stage") == "stuck"]
    assert stuck and stuck[0]["note"] == "replies refused"
    # It stopped on the refusals, not on the budget: every refused reply was a
    # real call, and the spend never reached the headroom.
    assert len(wrote(llm)) < 40 and result.metadata["spend_usd"] < 0.9


def test_a_shared_fact_can_be_stated_as_its_own_lemma():
    lemma = "lemma helper : True := by trivial"
    result, _, llm, _ = run([lemma, "exact key", "have key : True := by trivial",
                             "exact key"])
    lemmas = [e for e in result.metadata["events"] if e.get("kind") == "lemma"]
    assert lemmas and lemmas[0]["name"] == "helper" and lemmas[0]["accepted"]
    # It goes above the theorem, not inside its proof.
    assert result.solution.index(lemma) < result.solution.index("theorem demo")


def test_the_graded_theorem_cannot_be_restated_as_a_lemma():
    result, _, llm, _ = run(["theorem demo : True := by trivial"] * 30)
    assert result.metadata["accepted_by_repl"] is False
    assert "theorem demo : True := by trivial" not in result.solution


def test_the_graded_entry_point_is_the_framework_loop():
    import submission.agent as agent_mod
    from submission.framework_agent import FrameworkAgent

    assert isinstance(agent_mod.create_agent(), FrameworkAgent)


def test_a_reply_with_no_lean_is_told_so():
    result, _, llm, _ = run(["I think we should use induction here.",
                             "have key : True := by trivial", "exact key"])
    assert "contained no Lean" in wrote(llm)[1][1]
    assert result.metadata["accepted_by_repl"] is True


def test_the_writer_works_alone_while_it_is_working():
    """The mathematician costs a call, so it is what a stall buys, not a habit."""

    result, _, llm, _ = run(["have key : True := by trivial", "exact key"],
                            lines=("mathematician", "writer"))
    assert [model for model, _, _ in llm.calls] == ["mathematician", "mathematician"]
    assert not [e for e in result.metadata["events"] if e.get("kind") == "plan"]


def test_two_rejections_send_the_goal_back_to_the_mathematician():
    replies = ["have a : True := by first | (rfl; done)",
               "have b : True := by exact?",
               "have key : True := by trivial", "exact key"]
    result, _, llm, _ = run(replies, lines=("mathematician", "writer"))
    who = [model for model, _, _ in llm.calls]
    # write, write, then the mathematician: two Lean rejections mean the plan is
    # wrong, not the wording. The plan reaches the writer's next turn.
    # write, write, then the other model says what it was aiming at and takes
    # the goal over. The plan reaches whoever writes next.
    assert who[:4] == ["mathematician", "mathematician", "writer", "writer"]
    assert PLAN in wrote(llm)[2][1]
    assert result.metadata["accepted_by_repl"] is True


class HeavyLean(FakeLean):
    """`nlinarith` compiles; so does `linarith` in its place."""

    async def check_file(self, source, timeout_s=None):
        if "nlinarith" in source or "linarith" in source:
            return LeanCheck(True, [], False, False, 1)
        return await super().check_file(source)


def test_a_heavy_tactic_is_traded_for_a_cheap_one_when_the_file_still_compiles():
    lean, llm = HeavyLean(), FakeLLM(["nlinarith [sq_nonneg (a - b)]"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("m",), budget_usd=1.0, time_limit_s=3600.0))
    result = asyncio.run(agent.solve(
        Problem(id="demo", description="d", challenge=CHALLENGE), services))
    assert "nlinarith" not in result.solution and "linarith" in result.solution


def test_a_short_proof_is_not_tidied_at_all(monkeypatch):
    """The finish pass may not trade a file the grader accepts for a smaller one."""

    import submission.framework_agent as fa_mod

    replies = ["have spare : True := by trivial", "have key : True := by trivial",
               "exact key"]
    _, quiet, _, _ = run(replies)
    monkeypatch.setattr(fa_mod, "TIDY_ABOVE_BYTES", 0)
    _, busy, _, _ = run(replies)
    assert len(quiet.sources) < len(busy.sources)


TWO_GOALS = ("import Mathlib\n\ntheorem hard : False := by\n  sorry\n\n"
             "theorem easy : True := by\n  sorry\n")


class ParkLean:
    """Nothing closes `hard`; `trivial` closes `easy`."""

    def __init__(self):
        self.sources: list[str] = []

    async def check_file(self, source, timeout_s=None):
        self.sources.append(source)
        if "vm_probe" in source:
            return LeanCheck(True, [], False, False, 1)
        line = skip_line(source)
        if any(t in source for t in ("first", "exact?", "linarith")):
            return LeanCheck(False, [{"severity": "error", "pos": {"line": line or 1},
                                      "data": "linarith failed to find a contradiction"}],
                             True, False, 1)
        if not line:
            return LeanCheck("sorry" not in source, [], "sorry" in source, False, 1)
        head = source[: source.index("skip")]
        if head.rfind("theorem hard") > head.rfind("theorem easy"):
            return unsolved(line, "False")
        if "trivial" in head[head.rfind("theorem easy"):]:
            return LeanCheck(True, [{"severity": "warning", "pos": {"line": line},
                                     "data": "'skip' tactic does nothing"}],
                             False, False, 1)
        return unsolved(line, "True")


class GoalLLM:
    """Answers the goal it is shown, not the order it is asked in."""

    def __init__(self):
        self.calls: list[tuple[str, str, bool]] = []

    async def complete(self, *, model, messages, **kwargs):
        prompt = messages[-1]["content"]
        planning = "competition mathematician" in messages[0]["content"]
        self.calls.append((model, prompt, planning))
        text = PLAN if planning else ("trivial" if "⊢ True" in prompt else "linarith")
        return said(text, 0.001)


def run_two_goals():
    lean, llm = ParkLean(), GoalLLM()
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a", "model-b"), budget_usd=0.05,
                                  time_limit_s=600.0))
    problem = Problem(id="two", description="prove both", challenge=TWO_GOALS)
    return asyncio.run(agent.solve(problem, services)), lean, llm


def test_a_goal_nothing_closes_does_not_hold_the_other_one_hostage():
    result, lean, llm = run_two_goals()
    events = result.metadata["events"]
    parked = [e for e in events if e.get("stage") == "park"]
    assert parked and parked[0]["left"].startswith("⊢ False")
    assert parked[0]["now"].startswith("⊢ True")
    # The easy goal is closed, and the hard one keeps the run for the rest of
    # the budget rather than ending it.
    assert any("theorem easy : True := by\n  trivial\n" in s for s in lean.sources)
    assert events[-1] == {"stage": "stop", "note": "budget headroom"}
    # Both models saw the hard goal before the cursor left it.
    hard = [m for m, prompt, planning in llm.calls if not planning and "⊢ False" in prompt]
    assert set(hard[:4]) == {"model-a", "model-b"}


def test_what_was_said_about_the_parked_goal_does_not_follow_the_cursor():
    _, _, llm = run_two_goals()
    easy = [p for _, p, planning in llm.calls if not planning and "⊢ True" in p]
    assert easy
    # The hard goal's rejections and its plan belong to the hard goal.
    assert "Your last step was rejected" not in easy[0]
    assert "A mathematician was asked" not in easy[0]


def test_a_reply_cut_off_at_the_token_limit_is_not_sent_to_lean():
    lean, llm = FakeLean(), FakeLLM(["__cut__", "have key : True := by trivial",
                                     "exact key"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    problem = Problem(id="demo", description="prove it", challenge=CHALLENGE)
    result = asyncio.run(agent.solve(problem, services))
    assert {"kind": "cut", "by": "model-a"} in result.metadata["events"]
    # The half-written block never reached Lean, and never reached the file.
    assert not any("have half" in s for s in lean.sources)
    assert "have half" not in result.solution
    assert result.metadata["accepted_by_repl"] is True
    # The next turn is told what happened, not handed a syntax error to chase.
    assert "ran out of tokens" in wrote(llm)[1][1]


class WatchLLM:
    """Records the reasoning setting each model is sent."""

    def __init__(self, replies):
        self.replies, self.sent = list(replies), []

    async def complete(self, *, model, messages, reasoning=None, **kwargs):
        self.sent.append((model, reasoning))
        reply = self.replies.pop(0) if self.replies else "have junk : True := by trivial"
        return said(reply, 0.01)


def test_reasoning_is_decided_by_name_and_never_probed():
    lean = FakeLean()
    llm = WatchLLM(["have key : True := by trivial", "exact key"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("vendor/qwen3.5-flash", "vendor/gpt-oss"),
                                  budget_usd=1.0, time_limit_s=600.0))
    problem = Problem(id="demo", description="prove it", challenge=CHALLENGE)
    result = asyncio.run(agent.solve(problem, services))
    sent = dict(llm.sent)
    # A 400 for an unsupported setting ends the problem, so the model that
    # refuses to stop reasoning is never asked to.
    assert sent["vendor/qwen3.5-flash"] == {"enabled": False}
    assert all(r == {"effort": "low"} for m, r in llm.sent if "qwen" not in m)
    assert result.metadata["accepted_by_repl"] is True


BOTH = ("unsolved goals\ncase mp\nn : ℕ\n⊢ 7 ∣ 2 ^ n - 1 → 3 ∣ n\n\n"
        "case mpr\nn : ℕ\n⊢ 3 ∣ n → 7 ∣ 2 ^ n - 1")


class SplitLean:
    """Reports both goals at the declaration, the way Lean did on p09."""

    def __init__(self):
        self.sources: list[str] = []

    async def check_file(self, source, timeout_s=None):
        self.sources.append(source)
        if "vm_probe" in source:
            return LeanCheck(True, [], False, False, 1)
        if "first" in source or "exact?" in source:
            # Every alternative ends in `done`, so a block that does not close
            # the goal is an error, never a quiet success.
            return LeanCheck(False, [{"severity": "error", "pos": {"line": 4},
                                      "data": "linarith failed"}], True, False, 1)
        data = "unsolved goals\nn : ℕ\n⊢ 3 ∣ n" if "case mp =>" in source else BOTH
        return LeanCheck(False, [{"severity": "error", "pos": {"line": 3}, "data": data}],
                         True, False, 1)


def test_two_goals_behind_one_placeholder_are_split_once_and_only_once():
    lean, llm = SplitLean(), FakeLLM([])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a",), budget_usd=0.05, time_limit_s=600.0))
    problem = Problem(id="demo", description="prove it", challenge=CHALLENGE)
    result = asyncio.run(agent.solve(problem, services))
    splits = [e for e in result.metadata["events"] if e.get("stage") == "split"]
    assert len(splits) == 1 and splits[0]["goals"] == 2
    assert any("case mp =>" in s and "case mpr =>" in s for s in lean.sources)


def test_a_lemma_every_goal_can_reach_is_hoisted_and_then_proved_at_the_cursor():
    shared = "theorem key (n : ℕ) : n + 0 = n := by\n  sorry"
    lean, llm = FakeLean(), FakeLLM([shared, "have key2 : True := by trivial", "exact key"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    problem = Problem(id="demo", description="prove it", challenge=CHALLENGE)
    result = asyncio.run(agent.solve(problem, services))
    assert {"kind": "lemma", "by": "model-a", "name": "key", "accepted": True} in \
        result.metadata["events"]
    hoisted = next(s for s in lean.sources if "theorem key" in s)
    assert hoisted.index("theorem key") < hoisted.index("theorem demo")
    # Its own placeholder is the next cursor, so the lemma is proved like any goal.
    assert any("theorem key (n : ℕ) : n + 0 = n := by\n  skip" in s
               for s in lean.sources)


class StrandLean:
    """Answers the way Lean did on the bullet that broke p09."""

    def __init__(self):
        self.sources: list[str] = []

    async def check_file(self, source, timeout_s=None):
        self.sources.append(source)
        if "vm_probe" in source:
            return LeanCheck(True, [], False, False, 1)
        line = skip_line(source)
        if "first" in source or "exact?" in source:
            return LeanCheck(False, [{"severity": "error", "pos": {"line": line or 1},
                                      "data": "linarith failed"}], True, False, 1)
        if "intro h" in source:
            # One error on the bullet's own span, one on the declaration's.
            return LeanCheck(False, [
                {"severity": "error", "pos": {"line": 3, "column": 2},
                 "endPos": {"line": 3, "column": 11},
                 "data": "unsolved goals\ncase mp\n⊢ True"},
                {"severity": "error", "pos": {"line": 2, "column": 40},
                 "endPos": {"line": line, "column": 6},
                 "data": "unsolved goals\ncase mpr\n⊢ True"}], True, False, 1)
        if "exact key" in source and "have key" in source:
            return LeanCheck(True, [], False, False, 1)
        return unsolved(line)


def test_a_step_that_strands_a_goal_in_a_branch_is_refused():
    lean = StrandLean()
    llm = FakeLLM(["constructor\n· intro h", "have key : True := by trivial", "exact key"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a",), budget_usd=1.0, time_limit_s=600.0))
    problem = Problem(id="demo", description="prove it", challenge=CHALLENGE)
    result = asyncio.run(agent.solve(problem, services))
    assert "intro h" not in result.solution
    assert "nothing can get back to" in wrote(llm)[1][1]


SLOT_CHALLENGE = ("import Mathlib\n\nabbrev p_answer : ℕ := sorry\n\n"
                    "theorem demo : p_answer = 19 := by\n  sorry\n")


class SlotLean:
    """Prints whatever the `#eval` line says, the way the real probe reads it."""

    def __init__(self):
        self.sources: list[str] = []

    async def check_file(self, source, timeout_s=None):
        self.sources.append(source)
        if "first" in source or "exact?" in source:
            return LeanCheck(False, [{"severity": "error", "pos": {"line": 1},
                                      "data": "linarith failed"}], True, False, 1)
        printed = [l.split("#eval", 1)[1].strip() for l in source.splitlines()
                   if l.strip().startswith("#eval")]
        if printed:
            return LeanCheck(False, [{"severity": "info", "data": p} for p in printed],
                             True, False, 1)
        return unsolved(skip_line(source))


def test_more_probes_than_names_are_asked_for_again():
    lean = SlotLean()
    # The answer and two checks of it: the first printed value is what fills
    # the slot, so which line comes first decides the whole run.
    llm = FakeLLM(["#eval 19\n#eval 77 * 6\n#eval 21 * 22", "#eval 19"])
    services = FakeServices(lean, llm)
    agent = FrameworkAgent(Config(lines=("model-a",), budget_usd=0.03, time_limit_s=600.0))
    problem = Problem(id="demo", description="find it", challenge=SLOT_CHALLENGE)
    asyncio.run(agent.solve(problem, services))
    assert "exactly one per name" in wrote(llm)[1][1]
    assert any("abbrev p_answer : ℕ := 19" in s for s in lean.sources)
