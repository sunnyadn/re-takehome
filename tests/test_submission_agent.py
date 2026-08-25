"""Tests for the submission agent's search control, not for the harness."""

import asyncio
from types import SimpleNamespace

import pytest

import submission.agent as agent_mod
from re_harness import LLMCallError
from submission.agent import (
    COCKTAIL, Ledger, Line, SubmissionAgent, sweep_files, wrap_tactic,
)


def _walk(errors):
    line = Line(index=0, owner="m")
    seen = []
    for i, e in enumerate(errors):
        line.candidate, line.errors = f"file-{i}", e
        line.signature, line.feedback = f"sig-{e}", f"fb-{e}"
        seen.append((line.errors, line.candidate))
    return line, seen


def test_a_line_keeps_working_from_its_latest_file_even_when_it_got_worse():
    """Three of 15 model-won problems in the roll-back-free arms passed through
    an error increase on the way to a proof, including the only known wins on
    p09_imo1964 and p10_factorial_pow. Fewer Lean errors is not nearer a proof:
    fixing one error uncovers the ones it was masking."""

    line, seen = _walk([5, 2, 16, 17, 7, 7])
    assert [e for e, _ in seen] == [5, 2, 16, 17, 7, 7]
    assert line.candidate == "file-5"
    assert not hasattr(line, "best")


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


def test_surplus_lines_offsets_by_import_count():
    source = (
        "import Mathlib\n"      # 1
        "import Aesop\n"        # 2
        "\n"                    # 3
        "theorem t : True := by\n"  # 4
        "  trivial\n"           # 5
        "  norm_num\n"          # 6
    )
    messages = [{"severity": "error", "pos": {"line": 4},
                 "data": "No goals to be solved"}]
    assert agent_mod.surplus_lines(messages, source) == [6]


def test_surplus_lines_ignores_other_errors():
    source = "import Mathlib\ntheorem t : True := by\n  bogus\n"
    messages = [{"severity": "error", "pos": {"line": 2},
                 "data": "Unknown identifier `bogus`"}]
    assert agent_mod.surplus_lines(messages, source) == []


def test_drop_lines_removes_only_named_lines():
    source = "a\nb\nc\nd\n"
    assert agent_mod.drop_lines(source, [2, 4]) == "a\nc\n"


def test_drop_lines_keeps_declarations_below_the_drop():
    source = (
        "import Mathlib\n"
        "theorem helper : True := by\n"
        "  trivial\n"
        "  norm_num\n"
        "\n"
        "theorem required : True := by\n"
        "  trivial\n"
    )
    mended = agent_mod.drop_lines(source, [4])
    assert "theorem required" in mended
    assert "norm_num" not in mended


def test_extract_lean_drops_a_swallowed_fence():
    text = "```\n\n```lean\n\ntheorem t : True := by trivial\n```"
    out = agent_mod.extract_lean(text, fallback="import Mathlib\n")
    assert "```" not in out
    assert "theorem t" in out


def test_extract_lean_keeps_inline_backticks_in_docstrings():
    text = "```lean\n/-- Helper: `2 ^ 3` is small. -/\ntheorem t : True := by trivial\n```"
    out = agent_mod.extract_lean(text, fallback="import Mathlib\n")
    assert "`2 ^ 3`" in out


class _StuckLLM:
    """Answers with a fresh file each turn, so the loop reaches the Lean check."""

    def __init__(self):
        self.n = 0

    async def complete(self, **kwargs):
        self.n += 1
        response = _Response()
        response.content = (
            "```lean\nimport Mathlib\n\nlemma helper : True := by\n"
            f"  exact Nat.made_up_{self.n}\n\ntheorem required : True := by\n  trivial\n```"
        )
        return response


_TWO_DECLS = (
    "import Mathlib\n"          # 1
    "\n"                        # 2
    "lemma helper : True := by\n"  # 3
    "  exact Nat.made_up\n"     # 4
    "\n"                        # 5
    "theorem required : True := by\n"  # 6
    "  trivial\n"               # 7
)


def test_search_file_keeps_the_declarations_below_the_failure():
    out = agent_mod.search_file(_TWO_DECLS, 4)
    assert "all_goals apply?" in out
    assert "theorem required" in out, "the graded declaration was cut away"
    assert "Nat.made_up" not in out


def test_search_file_never_overwrites_the_statement():
    # An error reported on the `:= by` header must not replace the header.
    out = agent_mod.search_file(_TWO_DECLS, 3)
    assert "lemma helper : True := by" in out
    assert "all_goals apply?" in out


def test_suggestions_picks_only_try_this_info():
    messages = [
        {"severity": "info", "data": "Try this:\n  exact Nat.sqrt_le k"},
        {"severity": "info", "data": "some other note"},
        {"severity": "error", "data": "Try this: not an info"},
    ]
    assert agent_mod.suggestions(messages) == ["Try this:\n  exact Nat.sqrt_le k"]


class _SearchLean:
    """Fails the candidate with a missing name, answers the search with a hit."""

    def __init__(self):
        self.sources = []

    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        if "apply?" in source:
            return SimpleNamespace(
                accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
                messages=[{"severity": "info", "data": "Try this:\n  exact Nat.sqrt_le k"}],
            )
        return SimpleNamespace(
            accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
            messages=[{"severity": "error", "pos": {"line": 3},
                       "data": "Unknown constant `Nat.made_up`"}],
        )


def _advance_once(lean, challenge=_TWO_DECLS):
    agent = SubmissionAgent()
    agent._deadline = None
    line = Line(index=0, owner="qwen/qwen3.5-flash-02-23")
    line.candidate = challenge
    services = _Services(_StuckLLM())
    services.lean = lean
    services.checkpoint = lambda *a, **k: None
    problem = SimpleNamespace(challenge=challenge, description="s", id="t")
    ledger = Ledger()
    asyncio.run(agent._advance(problem, line, services, ledger, (), ()))
    return line, ledger


def test_a_missing_name_pulls_a_real_lemma_into_the_feedback():
    lean = _SearchLean()
    line, ledger = _advance_once(lean)
    assert any("apply?" in s for s in lean.sources), "no lemma search was run"
    assert "Nat.sqrt_le" in line.feedback, "the real lemma never reached the model"
    assert [e for e in ledger.events if e.get("stage") == "lemma_search"]


class _PlainFailLean(_SearchLean):
    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        return SimpleNamespace(
            accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
            messages=[{"severity": "error", "pos": {"line": 3}, "data": "unsolved goals"}],
        )


def test_no_search_when_no_name_is_missing():
    lean = _PlainFailLean()
    _advance_once(lean)
    assert not any("apply?" in s for s in lean.sources), "searched without a missing name"
