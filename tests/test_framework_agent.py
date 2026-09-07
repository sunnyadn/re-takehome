"""Screening replies and reading probe output, with no harness attached."""

from __future__ import annotations

import asyncio
import pathlib
from types import SimpleNamespace

from submission.config import ANSWER_TOKENS, Config, Ledger

from submission.board.types import STEP_TOKENS
from submission import prompts as pr
from submission import replies as rp
from submission import calls as cl

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
    for tokens in (STEP_TOKENS, ANSWER_TOKENS):
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


class _Recording:
    """Records what was asked of the provider. The reply shape is a real one,
    copied from an `llm_response` in outputs/board-2026-09-06/p08_sum_products."""

    def __init__(self):
        self.asked = []

    async def complete(self, **kwargs):
        self.asked.append(kwargs)
        return SimpleNamespace(content="omega", tool_calls=[], finish_reason="stop",
                               usage={"cost": 0.0, "completion_tokens": 12})


def _called(**extra):
    """One `_call`, and the keyword arguments the provider saw."""

    llm = _Recording()
    caller = cl.Caller(Config(lines=("qwen/qwen3.5-flash-02-23",)))
    services = SimpleNamespace(llm=llm, lean=None)
    asyncio.run(caller.call(extra.pop("model", "qwen/qwen3.5-flash-02-23"),
                            "prompt", 6000, services, Ledger(), **extra))
    return llm.asked[0]


def test_the_provider_is_asked_with_the_settings_the_recorded_runs_show():
    # Measured in outputs/board-2026-09-06/p08_sum_products: qwen was called at
    # temperature 0.4, max_tokens 6000, reasoning {"enabled": False}, no tools.
    asked = _called()
    assert asked["temperature"] == 0.4 and asked["max_tokens"] == 6000
    assert asked["reasoning"] == cl.NO_REASONING and "tools" not in asked
    # The line that does not narrate gets its reasoning back.
    assert _called(model="openai/gpt-oss-120b")["reasoning"] == cl.REASONING
    # `think` turns it on whoever is asked, because there the thinking is the answer.
    assert _called(think=True)["reasoning"] == cl.REASONING


def test_a_call_with_tools_names_the_one_function_it_will_accept():
    tool = {"type": "function", "function": {"name": "answer"}}
    asked = _called(tools=(tool,))
    assert asked["tools"] == [tool]
    assert asked["tool_choice"] == {"type": "function", "function": {"name": "answer"}}


def test_the_ladder_in_the_table_is_the_ladder_the_docs_draw():
    # The order lived in three places once. This is the one that can drift
    # silently: docs/ARCHITECTURE.md numbers the rungs and names each method.
    import re
    from submission.board_agent import LADDER

    doc = pathlib.Path("docs/ARCHITECTURE.md").read_text(encoding="utf-8")
    drawn = re.findall(r"^\| \d+ · [^|]*\| `run/ladder\.py::(\w+)`", doc, re.M)
    walked = [name for rung in LADDER for name in rung.calls]
    assert drawn == [n for n in walked if n != "consult"], (drawn, walked)


def test_a_goal_whose_statement_is_not_proved_yet_keeps_its_recall():
    # `recalled` is spent only once the statement is on the board somewhere
    # else. Spending it earlier would cost the goal its one free close when a
    # sibling branch proves the statement later, and no replay covers it: the
    # 16 recorded runs fire `recall` zero times.
    from submission.board_agent import LADDER
    from submission.board.types import Goal, Notes
    from submission.run.loop import Loop

    goal = Goal(34, 2, "rmo_2000_6", "⊢ 10 ≤ a * b", "10 ≤ a * b", 0)
    board = SimpleNamespace(proven={})
    called: list[str] = []

    class _Rungs:
        def __getattr__(self, name):
            async def rung(_goal):
                called.append(name)
                return False
            return rung

    loop = SimpleNamespace(rungs=LADDER, bb=board, ladder=_Rungs(),
                           run=SimpleNamespace(notes=Notes()))
    asyncio.run(Loop.climb(loop, goal))
    assert "recall" not in called
    assert loop.run.notes[goal.key].recalled is False
    assert loop.run.notes[goal.key].swept is True

    board.proven["10 ≤ a * b"] = "omega"
    asyncio.run(Loop.climb(loop, goal))
    assert called.count("recall") == 1
    assert loop.run.notes[goal.key].recalled is True
