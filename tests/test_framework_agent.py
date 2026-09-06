"""Screening replies and reading probe output, with no harness attached."""

from __future__ import annotations

from submission import framework_agent as fa
from submission import prompts as pr
from submission import replies as rp

FENCED = "Here you go:\n```lean\nhave h : True := by trivial\n```\n"


def test_a_fenced_step_survives_screening():
    assert rp.screen_step(FENCED) == "have h : True := by trivial"


def test_a_step_that_rewrites_the_file_is_refused():
    # A declaration is not refused here: the loop routes it above the theorem,
    # and refuses it there if it names something the problem already declares.
    assert rp.screen_step("theorem x : True := by trivial") != ""
    # An import line is not Lean tactic text: it is dropped, and the step it
    # came wrapped in survives rather than costing the whole call.
    assert rp.screen_step("import Mathlib\nintro x") == "intro x"
    assert rp.screen_step("decide using native_decide") == ""
    assert rp.screen_step("") == ""


def test_a_bare_placeholder_is_refused_but_branches_keep_theirs():
    assert rp.screen_step("have h : True := by sorry") == ""
    branch = rp.screen_step("induction n with\n| zero => sorry\n| succ k ih => sorry")
    assert branch.count("sorry") == 2


def test_only_the_triggered_notes_are_sent():
    assert pr.notes_for("linarith failed to find a contradiction").startswith("- Every")
    assert pr.notes_for("unsolved goals") == ""
    assert pr.notes_for("omega could not prove the goal").count("\n- ") == 0


def test_a_parse_error_from_an_older_dialect_is_named_as_such():
    # Measured across 9 runs: ~450 rejections ending in "expected command"
    # were Lean 3 spellings (`intro n hn,`, `cases h with a b`) and ~90
    # "unexpected token '!'" were `7!` with no `open Nat`; Lean's message
    # names neither and the models wrote the same line again.
    lean3 = pr.notes_for("error at {'line': 10, 'column': 12}: unexpected token ','; expected command")
    assert "Lean 3" in lean3 and "comma" in lean3
    assert "Lean 3" in pr.notes_for("unexpected token 'have'; expected command")
    assert "Lean 3" in pr.notes_for("unexpected token 'with'; expected command")
    bang = pr.notes_for("unexpected token '!'; expected command")
    assert "Nat.factorial" in bang and "open Nat" in bang
    assert "Lean 3" not in pr.notes_for("unexpected token ')'; expected command")


def test_probe_output_keeps_numerals_only():
    msgs = [
        {"severity": "info", "data": "19"},
        {"severity": "info", "data": "Try this: exact foo"},
        {"severity": "error", "data": "7"},
    ]
    assert rp.printed_numbers(msgs) == ["19"]


def test_a_step_that_does_nothing_is_refused():
    assert rp.screen_step("skip") == ""
    assert rp.screen_step("skip\n\nskip") == ""
    assert rp.screen_step("intro n\nskip") != ""


def test_the_calls_the_loop_makes_satisfy_the_harness_policy():
    """The model path spends money to exercise, so its contract is checked here.

    A rejected model name or an oversized max_tokens fails every call at once."""

    from re_harness.llm import LLMClient, MAX_OUTPUT_TOKENS
    from re_harness.models import ALLOWED_MODELS, PRICE_CEILINGS
    from submission.config import Config

    for model in Config().lines:
        assert model in ALLOWED_MODELS and model in PRICE_CEILINGS
    messages = [{"role": "system", "content": pr.FRAMEWORK_SYSTEM},
                {"role": "user", "content": "Write the next step."}]
    LLMClient._validate_messages(messages)
    for tokens in (fa.STEP_TOKENS, fa.ANSWER_TOKENS):
        assert isinstance(tokens, int) and 1 <= tokens <= MAX_OUTPUT_TOKENS


PROSE = """The problem asks me to prove that for positive reals the sum is at
least the product. I will introduce the variables first and then apply AM-GM.

intro n hn
have key : 0 < n := hn

That should close the goal."""


def test_prose_around_an_unfenced_step_is_dropped():
    # Measured on p08: qwen answers in prose as often as in Lean.
    assert rp.screen_step(PROSE) == "intro n hn\nhave key : 0 < n := hn"


def test_a_reply_that_is_only_prose_leaves_nothing():
    assert rp.screen_step("I think this goal needs a clever substitution.") == ""
