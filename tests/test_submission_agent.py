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
    """Fewer Lean errors is not nearer a proof: 3 of 15 wins came through an
    error increase, including the only ones on p09_imo1964 and
    p10_factorial_pow."""

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
            # The harness reports the status only inside the message.
            raise LLMCallError(
                f"OpenRouter returned HTTP {self.status}; the request was refused "
                f"and reported no cost: body"
            )
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
    assert retried == agent.config.max_retries


def test_surplus_lines_offsets_by_import_count():
    lines = ["import Mathlib", "import Aesop", "", "theorem t : True := by",
             "  trivial", "  norm_num"]
    source = "\n".join(lines) + "\n"
    surplus = lines.index("  norm_num") + 1
    messages = [{"severity": "error", "pos": {"line": 4},
                 "data": "No goals to be solved"}]
    assert agent_mod.surplus_lines(messages, source) == [surplus]


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


_TWO_DECL_LINES = ["import Mathlib", "", "lemma helper : True := by",
                   "  exact Nat.made_up", "", "theorem required : True := by",
                   "  trivial"]
_TWO_DECLS = "\n".join(_TWO_DECL_LINES) + "\n"


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


class _HugeHintLean(_SearchLean):
    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        if "apply?" in source:
            return SimpleNamespace(
                accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
                messages=[{"severity": "info", "data": "Try this:\n  exact Nat.sqrt_le k\n"
                                                       + "  -- goal\n" * 4000}] * 3,
            )
        return SimpleNamespace(
            accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
            messages=[{"severity": "error", "pos": {"line": 3},
                       "data": "Unknown constant `Nat.made_up`"}],
        )


class _SlowSearchLean(_SearchLean):
    """Each search burns wall-clock, so the time budget is what stops it."""

    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        if "apply?" in source:
            agent_mod.time.sleep(0.02)
            return SimpleNamespace(
                accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
                messages=[{"severity": "info", "data": "Try this:\n  exact Nat.sqrt_le k"}],
            )
        return SimpleNamespace(
            accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
            messages=[{"severity": "error", "pos": {"line": 3},
                       "data": "Unknown constant `Nat.made_up`"}],
        )


def test_the_search_budget_scales_with_the_time_limit():
    # A count cap measures the wrong thing, so the guard is cumulative seconds.
    small = agent_mod.Config(time_limit_s=1.0)
    big = agent_mod.Config(time_limit_s=100.0)
    assert (agent_mod.SEARCH_BUDGET_FRACTION * big.time_limit_s
            > agent_mod.SEARCH_BUDGET_FRACTION * small.time_limit_s)


def test_searching_stops_once_the_time_budget_is_gone():
    agent = SubmissionAgent(agent_mod.Config(time_limit_s=0.4))
    agent._deadline = None
    lean = _SlowSearchLean()
    services = _Services(_StuckLLM())
    services.lean = lean
    services.checkpoint = lambda *a, **k: None
    problem = SimpleNamespace(challenge=_TWO_DECLS, description="s", id="t")
    line, ledger = Line(index=0, owner="qwen/qwen3.5-flash-02-23"), Ledger()
    line.candidate = _TWO_DECLS
    for _ in range(12):
        asyncio.run(agent._advance(problem, line, services, ledger, (), ()))
    fired = [e for e in ledger.events if e.get("stage") == "lemma_search"]
    assert fired, "no search ran at all"
    assert len(fired) < 12, "the time budget never stopped the search"
    assert agent._search_spent_s >= agent_mod.SEARCH_BUDGET_FRACTION * 0.4


def test_the_hint_block_is_capped():
    line, _ = _advance_once(_HugeHintLean())
    assert "Nat.sqrt_le" in line.feedback
    assert len(line.feedback) < agent_mod.FEEDBACK_CHARS + agent_mod.HINT_CHARS + 500


def test_search_file_never_drops_a_graded_declaration():
    """Cutting a file to expose one goal twice destroyed declarations the
    grader needs byte-identical. This walks every line of every challenge."""

    from pathlib import Path

    root = Path(__file__).resolve().parent.parent / "sample-problems"
    checked = 0
    for problem in sorted(p for p in root.iterdir() if p.is_dir()):
        challenge = problem / "challenge.lean"
        if not challenge.exists():
            continue
        source = challenge.read_text()
        required = agent_mod.declared_names(source)
        for line in range(1, len(source.splitlines()) + 1):
            out = agent_mod.search_file(source, line)
            if out is None:
                continue
            checked += 1
            missing = [n for n in required if n not in out]
            assert not missing, f"{problem.name} line {line} dropped {missing}"
    assert checked > 50, f"only {checked} splices exercised, the walk is not covering"


_MIXED_ERRORS = [
    {"severity": "error", "pos": {"line": 3}, "data": "linarith failed to find a contradiction"},
    {"severity": "error", "pos": {"line": 7}, "data": "Unknown constant `Nat.made_up`"},
]


def test_source_lines_filters_to_the_matching_error():
    source = "import Mathlib\n" + "".join(f"line{i}\n" for i in range(1, 9))
    assert agent_mod.source_lines(_MIXED_ERRORS, source) == [4, 8]
    assert agent_mod.source_lines(_MIXED_ERRORS, source, agent_mod.MISSING_NAME) == [8]


class _MixedErrorLean(_SearchLean):
    """First error is not the missing name, so the search must skip past it."""

    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        if "apply?" in source:
            return SimpleNamespace(
                accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
                messages=[{"severity": "info", "data": "Try this:\n  exact Nat.sqrt_le k"}],
            )
        return SimpleNamespace(
            accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
            messages=[
                {"severity": "error", "pos": {"line": 2},
                 "data": "linarith failed to find a contradiction"},
                {"severity": "error", "pos": {"line": 6},
                 "data": "Unknown constant `Nat.made_up`"},
            ],
        )


def test_the_search_targets_the_invented_name_not_the_first_error():
    # 62% of triggering checks have an earlier, unrelated error; searching there
    # returns lemmas for a goal the hint text then misdescribes.
    lean = _MixedErrorLean()
    _advance_once(lean, challenge=_TWO_DECLS)
    spliced = [s for s in lean.sources if "apply?" in s]
    assert spliced, "no search ran"
    body = spliced[0].splitlines()
    at = next(i for i, l in enumerate(body, start=1) if "all_goals apply?" in l)
    assert at > 4, f"searched at line {at}, which is the unrelated first error"


def test_the_retry_pool_scales_with_the_clock():
    # Eight was sized for a 30-minute run of ~8 calls; a graded run makes ~35x
    # that, and exhausting the pool ends the run hours early.
    assert agent_mod.Config(time_limit_s=1800.0).max_retries == 8
    assert agent_mod.Config(time_limit_s=28800.0).max_retries == 128
    assert agent_mod.Config(time_limit_s=60.0).max_retries == 8


def test_the_agent_takes_its_retry_pool_from_its_config():
    agent = SubmissionAgent(agent_mod.Config(time_limit_s=28800.0))
    assert agent._retries_left == 128


def test_refused_before_generation_reads_the_harness_message():
    # The harness raises LLMCallError with the status only in the text, so the
    # agent must parse it rather than reach for an attribute that is not there.
    refused = LLMCallError("OpenRouter returned HTTP 429; the request was refused "
                           "and reported no cost: body")
    other = LLMCallError("OpenRouter returned HTTP 502; spend is uncertain: body")
    plain = LLMCallError("connection reset")
    assert agent_mod.refused_before_generation(refused)
    assert not agent_mod.refused_before_generation(other)
    assert not agent_mod.refused_before_generation(plain)


_SURRENDER = (
    "import Mathlib\n\n"
    "lemma dvd_of_mod_eq_zero {x y : ℕ} (h : y % x = 0) : x ∣ y :=\n"
    "  Nat.dvd_of_mod_eq_zero h\n"
)


class _SurrenderLLM:
    """Answers with a file that drops the graded theorem entirely."""

    async def complete(self, **kwargs):
        response = _Response()
        response.content = "```lean\n" + _SURRENDER + "```"
        return response


class _NoErrorLean:
    """Reports no errors and no acceptance, as a file with no goals does."""

    def __init__(self):
        self.sources = []

    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        return SimpleNamespace(accepted=False, has_sorry=False, timed_out=False,
                               container_restarted=False, messages=[])


def test_a_file_that_drops_the_graded_theorem_is_never_kept():
    """Observed on a real graded run: 7.2h and $0.61 submitted a 141-byte file
    with the theorem deleted, because deleting it left zero errors to count."""

    challenge = "import Mathlib\n\ntheorem required : True := by\n  sorry\n"
    agent = SubmissionAgent()
    services = _Services(_SurrenderLLM())
    services.lean = _NoErrorLean()
    kept = []
    services.checkpoint = lambda source, meta=None: kept.append(source)
    problem = SimpleNamespace(challenge=challenge, description="s", id="t")
    result = asyncio.run(agent.solve(problem, services))
    assert _SURRENDER not in kept, "a file without the graded theorem was checkpointed"
    assert "theorem required" in result.solution, "returned a file missing the theorem"


class _FixableLean(_SearchLean):
    """Fails on an invented name, and accepts the file once the real one is in."""

    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        ok = SimpleNamespace(accepted=True, has_sorry=False, timed_out=False,
                             container_restarted=False, messages=[])
        if "apply?" in source:
            return SimpleNamespace(
                accepted=False, has_sorry=False, timed_out=False,
                container_restarted=False,
                messages=[{"severity": "info",
                           "data": "Try this:\n  [apply] exact Nat.sqrt_le k"}])
        if "Nat.sqrt_le" in source:
            return ok
        return SimpleNamespace(
            accepted=False, has_sorry=False, timed_out=False,
            container_restarted=False,
            messages=[{"severity": "error", "pos": {"line": 3},
                       "data": "Unknown constant `Nat.made_up`"}])


def _advance_result(lean, challenge=_TWO_DECLS):
    agent = SubmissionAgent()
    agent._deadline = None
    line = Line(index=0, owner="qwen/qwen3.5-flash-02-23")
    line.candidate = challenge
    services = _Services(_StuckLLM())
    services.lean = lean
    services.checkpoint = lambda *a, **k: None
    problem = SimpleNamespace(challenge=challenge, description="s", id="t")
    ledger = Ledger()
    got = asyncio.run(agent._advance(problem, line, services, ledger, (), ()))
    return got, line, ledger


def test_a_lemma_lean_found_is_spliced_in_rather_than_requested():
    """The correct hint reached the model 3 times on rmo_2000_2 and was used 0
    times, so the tactic is applied instead of suggested."""

    got, line, ledger = _advance_result(_FixableLean())
    assert got is True, "a substitution that Lean accepts was not taken"
    assert "Nat.sqrt_le" in line.candidate
    assert "theorem required" in line.candidate, "the graded declaration was cut"
    assert [e for e in ledger.events if e.get("stage") == "substituted"]


def test_both_shapes_of_lean_suggestion_yield_a_tactic():
    """Captured from real runs: a lemma term and a tactic-advice block.

    The advice block is mostly prose, so only Lean's own marker is reliable."""

    lemma = "Try this:\n  [apply] exact lt_of_pow_lt_pow_left' 3 h2"
    advice = ("Try this:\n  [apply] ring_nf\n  \n  The `ring` tactic failed to "
              "close the goal. Use `ring_nf` to obtain a normal form.\n    \n  "
              "Note that `ring` works primarily in *commutative* rings.")
    assert agent_mod.suggested_tactics([lemma]) == ["exact lt_of_pow_lt_pow_left' 3 h2"]
    assert agent_mod.suggested_tactics([advice]) == ["ring_nf"]
    assert len(agent_mod.suggested_tactics([lemma, advice])) == 2


class _CountingLLM:
    """Records how many calls are in flight at once."""

    def __init__(self):
        self.live, self.peak, self.n = 0, 0, 0

    async def complete(self, **kwargs):
        self.live += 1
        self.peak = max(self.peak, self.live)
        self.n += 1
        await asyncio.sleep(0)
        try:
            response = _Response()
            response.content = "```lean\n" + _TWO_DECLS + "```"
            return response
        finally:
            self.live -= 1


class _NeverAcceptLean:
    async def check_file(self, source, **kwargs):
        return SimpleNamespace(accepted=False, has_sorry=False, timed_out=False,
                               container_restarted=False,
                               messages=[{"severity": "error", "pos": {"line": 3},
                                          "data": "unsolved goals"}])


def test_the_slots_run_concurrently_rather_than_taking_turns():
    """91.5% of wall clock was spent waiting on serial calls, while one line
    idled through the other's 418-second wait."""

    llm = _CountingLLM()
    agent = SubmissionAgent(agent_mod.Config(time_limit_s=1800.0, max_turns_per_line=1))
    services = _Services(llm)
    services.lean = _NeverAcceptLean()
    services.checkpoint = lambda *a, **k: None
    problem = SimpleNamespace(challenge=_TWO_DECLS, description="s", id="t")
    asyncio.run(agent.solve(problem, services))
    slots = len(agent_mod.SLOT_TEMPERATURES) * 2
    assert llm.peak > 1, "calls were still serialised"
    assert llm.peak >= slots, f"peak {llm.peak} below the {slots} slots"


class _PartiallyFixableLean(_SearchLean):
    """The spliced lemma clears one error of three and leaves the rest."""

    def _errors(self, n):
        return SimpleNamespace(
            accepted=False, has_sorry=False, timed_out=False,
            container_restarted=False,
            messages=[{"severity": "error", "pos": {"line": 3 + i},
                       "data": "Unknown constant `Nat.made_up`"} for i in range(n)])

    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        if "apply?" in source:
            return SimpleNamespace(
                accepted=False, has_sorry=False, timed_out=False,
                container_restarted=False,
                messages=[{"severity": "info",
                           "data": "Try this:\n  [apply] exact Nat.sqrt_le k"}])
        return self._errors(1 if "Nat.sqrt_le" in source else 3)


def test_a_substitution_that_only_reduces_errors_is_still_taken():
    """No recorded search ever ran on a one-error file, so demanding the whole
    file compile made the mechanism unreachable."""

    got, line, ledger = _advance_result(_PartiallyFixableLean())
    assert got is False, "a file Lean still rejects was reported as solved"
    assert "Nat.sqrt_le" in line.candidate, "the improvement was discarded"
    assert line.errors == 1, f"errors not recomputed after the splice: {line.errors}"
    assert [e for e in ledger.events if e.get("stage") == "substituted"]


class _WorseningLean(_PartiallyFixableLean):
    """The spliced lemma makes the file worse, so it must be refused."""

    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        if "apply?" in source:
            return SimpleNamespace(
                accepted=False, has_sorry=False, timed_out=False,
                container_restarted=False,
                messages=[{"severity": "info",
                           "data": "Try this:\n  [apply] exact Nat.sqrt_le k"}])
        return self._errors(5 if "Nat.sqrt_le" in source else 3)


def test_a_substitution_that_adds_errors_is_refused():
    got, line, ledger = _advance_result(_WorseningLean())
    assert got is False
    assert "Nat.sqrt_le" not in line.candidate, "a worse file was adopted"
    assert not [e for e in ledger.events if e.get("stage") == "substituted"]


def test_a_truncated_proof_asks_lean_with_a_bare_sorry():
    src = ("import Mathlib\n\ntheorem t : True := by\n  have h : 1 = 1 := by\n"
           "    made_up_tactic\n  trivial\n")
    cut = agent_mod.resume_file(src, 5)
    assert cut is not None and "sorry" in cut
    assert "trace_state" not in cut, "trace_state does not survive the cut"


def test_open_goals_refuses_a_prefix_that_still_has_a_real_error():
    """A prefix is only verified when nothing but the goal is left."""

    messages = [{"severity": "error", "data": "unsolved goals\n⊢ x = 9"},
                {"severity": "error", "data": "Unknown identifier `foo`"}]
    assert agent_mod.open_goals(messages) == []


def test_open_goals_returns_the_goal_when_only_the_goal_is_left():
    messages = [{"severity": "error", "data": "unsolved goals\nx : ℕ\n⊢ x = 9"}]
    assert agent_mod.open_goals(messages) == ["x : ℕ\n⊢ x = 9"]


class _ResumableLean(_SearchLean):
    """Rejects the file, and reports only an open goal once it is truncated."""

    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        if "apply?" in source:
            return SimpleNamespace(accepted=False, has_sorry=False, timed_out=False,
                                   container_restarted=False, messages=[])
        if "sorry" in source:
            return SimpleNamespace(
                accepted=False, has_sorry=True, timed_out=False,
                container_restarted=False,
                messages=[{"severity": "error", "pos": {"line": 3},
                           "data": "unsolved goals\n⊢ 2 = 2"}])
        return SimpleNamespace(
            accepted=False, has_sorry=False, timed_out=False,
            container_restarted=False,
            messages=[{"severity": "error", "pos": {"line": 3},
                       "data": "Unknown constant `Nat.made_up`"}])


def test_the_verified_prefix_reaches_the_repair_prompt():
    """The prefix carries a sorry, so it must never become the candidate."""

    got, line, ledger = _advance_result(_ResumableLean())
    assert got is False
    assert line.resume is not None, "the compiled prefix was not kept"
    assert line.resume[1] == "⊢ 2 = 2"
    assert "sorry" not in line.candidate, "a file with a sorry became the candidate"
    prompt = agent_mod.repairer_user(
        SimpleNamespace(id="t", description="s", challenge=_TWO_DECLS), line, False)
    assert "already compiles" in prompt and "⊢ 2 = 2" in prompt
    assert [e for e in ledger.events if e.get("stage") == "resume"]
