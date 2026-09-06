"""The loop's control: accept, discard, settle, take turns, stop on budget."""

from __future__ import annotations

import asyncio
import time

from re_harness import LLMCallError, Problem
from re_harness.lean import LeanCheck
from submission.config import Config
from submission.framework_agent import FrameworkAgent

CHALLENGE = "import Mathlib\n\ntheorem demo : True := by\n  sorry\n"


PLAN = "Take the obvious route: state the fact and close it."


def said(content: str, cost: float, finish: str = "stop"):
    return type("R", (), {"content": content, "usage": {"cost": cost},
                          "finish_reason": finish, "tool_calls": None})()


class FakeServices:
    def __init__(self, lean, llm):
        self.lean, self.llm, self.checkpoints = lean, llm, []

    def checkpoint(self, source, metadata=None):
        self.checkpoints.append(source)


ANSWER_CHALLENGE = ("import Mathlib\n\nabbrev p_answer : ℕ := sorry\n\n"
                    "theorem demo : p_answer = 77 := by\n  sorry\n")


# The graded theorem first, so the cursor starts there and the lemma is open
# behind it, which is where p09 left its hoisted fact once the cursor moved on.
LEMMA_BEHIND = ("import Mathlib\n\ntheorem demo : True := by\n  sorry\n\n"
                "lemma helper : True := by\n  induction' n with n ih\n  sorry\n")


def test_the_graded_entry_point_is_the_board():
    import submission.agent as agent_mod
    from submission.board_agent import BoardAgent

    assert isinstance(agent_mod.create_agent(), BoardAgent)


TWO_GOALS = ("import Mathlib\n\ntheorem hard : False := by\n  sorry\n\n"
             "theorem easy : True := by\n  sorry\n")


BOTH = ("unsolved goals\ncase mp\nn : ℕ\n⊢ 7 ∣ 2 ^ n - 1 → 3 ∣ n\n\n"
        "case mpr\nn : ℕ\n⊢ 3 ∣ n → 7 ∣ 2 ^ n - 1")


SLOT_CHALLENGE = ("import Mathlib\n\nabbrev p_answer : ℕ := sorry\n\n"
                    "theorem demo : p_answer = 19 := by\n  sorry\n")


TWO = ("import Mathlib\n\ntheorem demo : True := by\n  sorry\n\n"
       "theorem demo_b : True := by\n  sorry\n")


def test_an_answer_slot_is_a_declaration_but_not_a_second_theorem():
    import submission.framework as fw
    assert fw.graded_theorems(ANSWER_CHALLENGE) == 1
    assert fw.graded_theorems(TWO) == 2


def test_a_reply_that_opens_with_by_keeps_its_block_shape():
    # Measured on p09: 13 of gpt-oss's 34 replies opened with a lone `by`, and
    # each came out with its first line dedented and the rest not, which Lean
    # read as `unexpected token 'have'; expected command`.
    from submission.replies import screen_step
    bare = "by\n  intro h\n  have x : True := by\n    trivial\n  exact x"
    want = "intro h\nhave x : True := by\n  trivial\nexact x"
    assert screen_step(bare) == want
    assert screen_step("```lean\n" + bare + "\n```") == want
    assert screen_step("Sure.\n\n" + bare) == want
