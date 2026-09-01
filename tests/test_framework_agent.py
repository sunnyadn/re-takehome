"""Screening replies and reading probe output, with no harness attached."""

from __future__ import annotations

from submission import framework_agent as fa

FENCED = "Here you go:\n```lean\nhave h : True := by trivial\n```\n"


def test_a_fenced_step_survives_screening():
    assert fa.screen_step(FENCED) == "have h : True := by trivial"


def test_a_step_that_rewrites_the_file_is_refused():
    # A declaration is not refused here: the loop routes it above the theorem,
    # and refuses it there if it names something the problem already declares.
    assert fa.screen_step("theorem x : True := by trivial") != ""
    assert fa.screen_step("import Mathlib\nintro x") == ""
    assert fa.screen_step("decide using native_decide") == ""
    assert fa.screen_step("") == ""


def test_a_bare_placeholder_is_refused_but_branches_keep_theirs():
    assert fa.screen_step("have h : True := by sorry") == ""
    branch = fa.screen_step("induction n with\n| zero => sorry\n| succ k ih => sorry")
    assert branch.count("sorry") == 2


def test_only_the_triggered_notes_are_sent():
    assert fa.notes_for("linarith failed to find a contradiction").startswith("- Every")
    assert fa.notes_for("unsolved goals") == ""
    assert fa.notes_for("omega could not prove the goal").count("\n- ") == 0


def test_probe_output_keeps_numerals_only():
    msgs = [
        {"severity": "info", "data": "19"},
        {"severity": "info", "data": "Try this: exact foo"},
        {"severity": "error", "data": "7"},
    ]
    assert fa.printed_numbers(msgs) == ["19"]


def test_a_step_that_does_nothing_is_refused():
    assert fa.screen_step("skip") == ""
    assert fa.screen_step("skip\n\nskip") == ""
    assert fa.screen_step("intro n\nskip") != ""


def test_the_calls_the_loop_makes_satisfy_the_harness_policy():
    """The model path spends money to exercise, so its contract is checked here.

    A rejected model name or an oversized max_tokens fails every call at once."""

    from re_harness.llm import LLMClient, MAX_OUTPUT_TOKENS
    from re_harness.models import ALLOWED_MODELS, PRICE_CEILINGS
    from submission.agent import Config

    for model in Config().lines:
        assert model in ALLOWED_MODELS and model in PRICE_CEILINGS
    messages = [{"role": "system", "content": fa.FRAMEWORK_SYSTEM},
                {"role": "user", "content": "Write the next step."}]
    LLMClient._validate_messages(messages)
    for tokens in (fa.STEP_TOKENS, fa.ANSWER_TOKENS):
        assert isinstance(tokens, int) and 1 <= tokens <= MAX_OUTPUT_TOKENS
