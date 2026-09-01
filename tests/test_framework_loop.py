"""The loop's control: accept, discard, settle, take turns, stop on budget."""

from __future__ import annotations

import asyncio

from re_harness import Problem
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
            if line:
                return LeanCheck(False, [{"severity": "error", "pos": {"line": line},
                                          "data": "no goals to be solved"}], False, False, 1)
            return LeanCheck(True, [], False, False, 1)
        if "first" in source or "exact?" in source:
            return LeanCheck(False, [{"severity": "error", "pos": {"line": line or 1},
                                      "data": "linarith failed to find a contradiction"}],
                             True, False, 1)
        return unsolved(line)


class FakeLLM:
    def __init__(self, replies):
        self.replies, self.calls = list(replies), []

    async def complete(self, *, model, messages, **kwargs):
        self.calls.append((model, messages[-1]["content"]))
        reply = self.replies.pop(0) if self.replies else "have junk : True := by trivial"
        return type("R", (), {"content": reply, "usage": {"cost": 0.01}})()


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
    assert len(llm.calls) == 2


def test_a_rejected_step_is_removed_and_the_other_model_gets_the_next_turn():
    replies = ["have bad : True := by first | (rfl; done)",
               "have worse : True := by exact?",
               "have key : True := by trivial", "exact key"]
    result, _, llm, _ = run(replies)
    authors = [model for model, _ in llm.calls]
    # Two rejections on one goal, then the other model gets it.
    assert authors[:3] == ["model-a", "model-a", "model-b"]
    assert "bad" not in result.solution and "worse" not in result.solution
    assert result.metadata["accepted_by_repl"] is True


def test_lean_s_own_words_are_carried_into_the_next_attempt():
    replies = ["have bad : True := by first | (rfl; done)",
               "have key : True := by trivial", "exact key"]
    _, _, llm, _ = run(replies)
    assert "linarith failed" in llm.calls[1][1]
    assert "Every closer before nlinarith" in llm.calls[1][1]
    # The closers are the harness's attempt, not the model's; saying otherwise
    # asks the model to correct a step it never wrote.
    assert "Your last step" not in llm.calls[0][1]
    assert "A search attempt on this goal was rejected" in llm.calls[0][1]
    assert "Your last step was rejected" in llm.calls[1][1]
    assert llm.calls[1][0] == llm.calls[0][0]


def test_the_loop_stops_asking_once_the_budget_headroom_is_gone():
    result, _, llm, _ = run(["have junk : True := by trivial"] * 20, budget=0.02)
    assert len(llm.calls) <= 2
    assert result.metadata["accepted_by_repl"] is False
    assert result.metadata["spend_usd"] <= 0.02


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
