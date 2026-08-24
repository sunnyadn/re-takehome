"""Tests for the submission agent's search control, not for the harness."""

import asyncio

import pytest

import submission.agent as agent_mod
from re_harness import LLMCallError
from submission.agent import (
    COCKTAIL, Ledger, Line, SubmissionAgent, sweep_files, wrap_tactic,
)


def _walk(errors, accepted=False):
    line = Line(index=0, owner="m")
    seen = []
    for i, e in enumerate(errors):
        line.candidate, line.errors = f"file-{i}", e
        line.signature, line.feedback = f"sig-{e}", f"fb-{e}"
        line.keep_best(accepted)
        seen.append((line.errors, line.candidate))
    return line, seen


def test_regression_is_rolled_back_to_the_best_file():
    # The trajectory a baseline run actually produced on putnam_2020_a2.
    line, seen = _walk([5, 2, 16, 17, 7, 7])
    assert [e for e, _ in seen] == [5, 2, 2, 2, 2, 2]
    assert all(c == "file-1" for _, c in seen[1:])
    assert line.rejected


def test_monotone_descent_is_never_rolled_back():
    line, seen = _walk([9, 6, 3, 0])
    assert [e for e, _ in seen] == [9, 6, 3, 0]
    assert not line.rejected


def test_an_accepted_file_survives_a_higher_error_count():
    line = Line(index=0, owner="m")
    line.candidate, line.errors = "good", 1
    line.keep_best(False)
    line.candidate, line.errors = "accepted", 3
    assert line.keep_best(True) is False
    assert line.candidate == "accepted"


def test_the_rejection_memo_stays_short_and_deduplicated():
    line, _ = _walk([1, 9, 9, 8, 7, 6])
    assert len(line.rejected) <= 3
    assert len(set(line.rejected)) == len(line.rejected)


def test_every_cocktail_alternative_is_parenthesised():
    # A bare `;` truncates the enclosing `first` block and silently drops the
    # alternatives after it, which once cost the sweep three quarters of its hits.
    for tactic in COCKTAIL:
        assert wrap_tactic(tactic).startswith("(") and wrap_tactic(tactic).endswith("; done)")


def test_sweep_declines_a_file_with_a_sorry_outside_a_proof():
    source = "import Mathlib\n\ndef answer : Nat := sorry\n\ntheorem t : True := by\n  sorry\n"
    assert sweep_files(source) == []


class _Usage(dict):
    pass


class _Response:
    def __init__(self):
        self.content = "ok"
        self.finish_reason = "stop"
        self.usage = {"cost": 0.001}


class _FlakyLLM:
    """Refuses `refusals` times with `status`, then answers."""

    def __init__(self, refusals, status=429):
        self.refusals, self.status, self.calls = refusals, status, 0

    async def complete(self, **kwargs):
        self.calls += 1
        if self.calls <= self.refusals:
            raise LLMCallError(f"HTTP {self.status}", status_code=self.status)
        return _Response()


class _Services:
    def __init__(self, llm):
        self.llm = llm


def _call_once(llm):
    agent = SubmissionAgent()
    ledger = Ledger()
    out = asyncio.run(agent._call(
        "qwen/qwen3.5-flash-02-23", "sys", "user", 100,
        _Services(llm), ledger, 0, "repair", False,
    ))
    return out, ledger


def test_a_refusal_is_retried_until_it_answers(monkeypatch):
    monkeypatch.setattr(agent_mod, "RETRY_BACKOFF_S", (0.0, 0.0, 0.0))
    llm = _FlakyLLM(refusals=2)
    out, ledger = _call_once(llm)
    assert out == "ok" and llm.calls == 3
    assert sum("retry in" in str(e.get("note", "")) for e in ledger.events) == 2


def test_retries_are_bounded_and_then_the_error_escapes(monkeypatch):
    monkeypatch.setattr(agent_mod, "RETRY_BACKOFF_S", (0.0, 0.0, 0.0))
    llm = _FlakyLLM(refusals=99)
    with pytest.raises(LLMCallError):
        _call_once(llm)
    assert llm.calls == 4


def test_an_error_that_poisons_accounting_is_not_retried(monkeypatch):
    # 500 marks spend unknown, which zeroes the problem however good the proof
    # is, so repeating the call would only burn time.
    monkeypatch.setattr(agent_mod, "RETRY_BACKOFF_S", (0.0, 0.0, 0.0))
    llm = _FlakyLLM(refusals=99, status=500)
    with pytest.raises(LLMCallError):
        _call_once(llm)
    assert llm.calls == 1


def test_the_stop_margin_never_eats_a_quarter_of_a_short_run():
    # The 8-hour floor used to swallow 47% of a 30-minute run.
    from submission.agent import Config
    short, graded = Config(time_limit_s=1800.0), Config(time_limit_s=28800.0)
    assert short.stop_margin_s <= 0.25 * 1800.0
    assert short.last_turn_start_s / 1800.0 > 0.6
    # The graded setting must be untouched by the cap.
    assert graded.last_turn_start_s == 25800.0


def test_retries_are_capped_across_the_whole_problem(monkeypatch):
    # Each refusal keeps its reservation as permanent exposure, so an
    # unbounded per-call retry closes the ledger on a long run.
    monkeypatch.setattr(agent_mod, "RETRY_BACKOFF_S", (0.0, 0.0, 0.0))
    agent = SubmissionAgent()
    llm, ledger = _FlakyLLM(refusals=99), Ledger()
    calls = 0
    for _ in range(6):
        try:
            asyncio.run(agent._call("qwen/qwen3.5-flash-02-23", "s", "u", 100,
                                    _Services(llm), ledger, 0, "repair", False))
        except LLMCallError:
            pass
    retried = sum("retry in" in str(e.get("note", "")) for e in ledger.events)
    assert retried == agent_mod.MAX_RETRIES_PER_PROBLEM
