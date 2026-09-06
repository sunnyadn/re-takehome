"""Tests for the submission agent's search control, not for the harness."""

import asyncio
from types import SimpleNamespace


import submission.agent as agent_mod
import submission.config as config
import submission.contract as contract
import submission.sweep as sweep
from re_harness import LLMCallError
from submission.config import Ledger
from submission.sweep import COCKTAIL, sweep_files, wrap_tactic


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


def test_the_stop_margin_never_eats_a_quarter_of_a_short_run():
    # The 8-hour floor used to swallow 47% of a 30-minute run.
    from submission.config import Config
    short, graded = Config(time_limit_s=1800.0), Config(time_limit_s=28800.0)
    assert short.stop_margin_s <= 0.25 * 1800.0
    assert short.last_turn_start_s / 1800.0 > 0.6
    # The graded setting must be untouched by the cap.
    assert graded.last_turn_start_s == 25800.0


def test_file_coordinates_moves_lean_positions_down_by_the_import_lines():
    # Measured on rmo_2000_6 (h59a, 2026-09-03 09:50Z): with the challenge's
    # two imports kept plus import Mathlib, every goal read as empty and the
    # run stopped after 25 s with "no goal left to work on": the REPL client
    # strips import lines and the board was calibrated for exactly one.
    import asyncio
    from re_harness.lean import LeanCheck

    class Raw:
        async def check_file(self, source, timeout_s=None):
            return LeanCheck(False, [{"severity": "error", "pos": {"line": 4}, "endPos": {"line": 5},
                                      "data": "unsolved goals\n⊢ True"}], True, False, 1)
    lean = contract.FileCoordinates(Raw())
    three = "import A\nimport B\nimport Mathlib\n\ntheorem t : True := by\n  sorry\n"
    one = "import Mathlib\n\ntheorem t : True := by\n  sorry\n"
    assert asyncio.run(lean.check_file(three)).messages[0]["pos"]["line"] == 7
    assert asyncio.run(lean.check_file(three)).messages[0]["endPos"]["line"] == 8
    assert asyncio.run(lean.check_file(one)).messages[0]["pos"]["line"] == 5
    # idempotent wrapping
    services = type("S", (), {})(); services.lean = Raw()
    contract.in_file_coordinates(services); inner = services.lean
    assert contract.in_file_coordinates(services).lean is inner


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


def test_suggestions_picks_only_try_this_info():
    messages = [
        {"severity": "info", "data": "Try this:\n  exact Nat.sqrt_le k"},
        {"severity": "info", "data": "some other note"},
        {"severity": "error", "data": "Try this: not an info"},
    ]
    assert contract.suggestions(messages) == ["Try this:\n  exact Nat.sqrt_le k"]


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


class _PlainFailLean(_SearchLean):
    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        return SimpleNamespace(
            accepted=False, has_sorry=False, timed_out=False, container_restarted=False,
            messages=[{"severity": "error", "pos": {"line": 3}, "data": "unsolved goals"}],
        )


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


_MIXED_ERRORS = [   # file coordinates, as FileCoordinates hands them on
    {"severity": "error", "pos": {"line": 4}, "data": "linarith failed to find a contradiction"},
    {"severity": "error", "pos": {"line": 8}, "data": "Unknown constant `Nat.made_up`"},
]


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


def test_refused_before_generation_reads_the_harness_message():
    # The harness raises LLMCallError with the status only in the text, so the
    # agent must parse it rather than reach for an attribute that is not there.
    refused = LLMCallError("OpenRouter returned HTTP 429; the request was refused "
                           "and reported no cost: body")
    other = LLMCallError("OpenRouter returned HTTP 502; spend is uncertain: body")
    plain = LLMCallError("connection reset")
    assert contract.refused_before_generation(refused)
    assert not contract.refused_before_generation(other)
    assert not contract.refused_before_generation(plain)


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


def test_both_shapes_of_lean_suggestion_yield_a_tactic():
    """Captured from real runs: a lemma term and a tactic-advice block.

    The advice block is mostly prose, so only Lean's own marker is reliable."""

    lemma = "Try this:\n  [apply] exact lt_of_pow_lt_pow_left' 3 h2"
    advice = ("Try this:\n  [apply] ring_nf\n  \n  The `ring` tactic failed to "
              "close the goal. Use `ring_nf` to obtain a normal form.\n    \n  "
              "Note that `ring` works primarily in *commutative* rings.")
    assert contract.suggested_tactics([lemma]) == ["exact lt_of_pow_lt_pow_left' 3 h2"]
    assert contract.suggested_tactics([advice]) == ["ring_nf"]
    assert len(contract.suggested_tactics([lemma, advice])) == 2


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


class _SurplusLean(_SearchLean):
    """One surplus tactic, whose removal clears that error but not the others."""

    def _msgs(self, surplus):
        out = [{"severity": "error", "pos": {"line": 3},
                "data": "no goals to be solved"}] if surplus else []
        out.append({"severity": "error", "pos": {"line": 2}, "data": "still broken"})
        return SimpleNamespace(accepted=False, has_sorry=False, timed_out=False,
                               container_restarted=False, messages=out)

    async def check_file(self, source, **kwargs):
        self.sources.append(source)
        if "apply?" in source or "sorry" in source:
            return SimpleNamespace(accepted=False, has_sorry=False, timed_out=False,
                                   container_restarted=False, messages=[])
        return self._msgs("Nat.made_up" in source)


def test_a_mend_that_cuts_a_graded_declaration_is_refused():
    """surplus_lines can point at the statement itself; scoring_faults is the
    only thing standing between that and a file the grader scores zero."""

    from submission.contract import scoring_faults
    from submission.framework import drop_lines
    cut = drop_lines(_TWO_DECLS, [6])
    assert scoring_faults(cut, (), _TWO_DECLS), "dropping the statement raised no fault"


def test_split_candidates_are_only_built_for_a_decomposable_goal():
    """Twelve extra Lean checks are worth paying only where a split can help."""

    iff = "theorem t : True ↔ True := by\n  sorry\n"
    flat = "theorem t (x : ℝ) : x = x := by\n  sorry\n"
    assert len(sweep.split_files(iff, ("rfl",))) == len(sweep.SPLITTERS)
    assert sweep.split_files(flat, ("rfl",)) == []

