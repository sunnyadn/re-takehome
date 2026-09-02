import asyncio
import re
import time

from re_harness import Problem
from re_harness.lean import LeanCheck
from submission.agent import Config
from submission.board_agent import (
    Board, BoardAgent, Goal, interpret, read_board, render_all,
)
from tests.test_framework_loop import FakeServices, said

ONE = "import Mathlib\n\ntheorem demo : True := by\n  sorry\n"
TWO = ("import Mathlib\n\ntheorem demo : True := by\n  sorry\n\n"
       "theorem demo_b : True := by\n  sorry\n")
HEAD = re.compile(r"^\s*(?:theorem|lemma)\s+(\w+)")


class BoardLean:
    """Every `skip` reports its own goal, whose hypotheses are the `have`s above
    it in the same declaration. `exact key` closes when `key` is in scope."""

    def __init__(self):
        self.sources: list[str] = []

    async def check_file(self, source, timeout_s=None):
        self.sources.append(source)
        if "vm_probe" in source:
            return LeanCheck(True, [], False, False, 1)
        messages, decl, haves = [], "", []
        for i, line in enumerate(source.split("\n"), start=1):
            head = HEAD.match(line)
            if head:
                decl, haves = head.group(1), []
                continue
            body = line.strip()
            if body.startswith("have "):
                haves.append(body.split()[1])
            if body.startswith(("first", "exact?", "linarith")):
                messages.append({"severity": "error", "pos": {"line": i - 1},
                                 "endPos": {"line": i - 1},
                                 "data": "linarith failed to find a contradiction"})
            if body == "skip":
                closed = any(f"exact {h}" in source.split("\n")[j]
                             for j in range(i - 2, -1, -1)
                             if HEAD.match(source.split("\n")[j]) is None
                             for h in haves) if haves else False
                if closed:
                    continue
                hyps = "".join(f"{h} : True\n" for h in haves)
                messages.append({"severity": "error", "pos": {"line": i - 2},
                                 "endPos": {"line": i - 1},
                                 "data": f"unsolved goals\n{hyps}⊢ {decl}"})
        errors = [m for m in messages if m["severity"] == "error"]
        return LeanCheck(not errors, messages, "sorry" in source, False, 1)


class ScriptLLM:
    """Replies chosen by who is asking; each model has its own queue."""

    def __init__(self, scripts: dict[str, list[str]], delay: dict[str, float] | None = None):
        self.scripts = {k: list(v) for k, v in scripts.items()}
        self.delay = delay or {}
        self.calls: list[tuple[str, str]] = []

    async def complete(self, *, model, messages, **kwargs):
        prompt = messages[-1]["content"]
        self.calls.append((model, prompt))
        if self.delay.get(model):
            await asyncio.sleep(self.delay[model])
        if "competition mathematician" in messages[0]["content"]:
            return said("Take the obvious route.", 0.001)
        queue = self.scripts.get(model, [])
        reply = queue.pop(0) if queue else "have junk : True := by trivial"
        return said(reply, 0.01)


def run(challenge, scripts, delay=None, lines=("model-a", "model-b"), time_limit=600.0):
    lean, llm = BoardLean(), ScriptLLM(scripts, delay)
    agent = BoardAgent(Config(lines=lines, budget_usd=1.0, time_limit_s=time_limit))
    problem = Problem(id="demo", description="prove it", challenge=challenge)
    started = time.monotonic()
    result = asyncio.run(agent.solve(problem, FakeServices(lean, llm)))
    return result, lean, llm, time.monotonic() - started


def steps(result):
    return [e for e in result.metadata["events"] if e.get("kind") == "step"]


def test_every_placeholder_is_rendered_as_skip_at_once():
    assert render_all(TWO).count("skip") == 2 and "sorry" not in render_all(TWO)


def test_the_board_reads_one_goal_per_placeholder_with_its_own_context():
    text = ("import Mathlib\n\ntheorem demo : True := by\n  have k : True := by\n"
            "    sorry\n  sorry\n\ntheorem demo_b : True := by\n  sorry\n")
    check = asyncio.run(BoardLean().check_file(render_all(text)))
    board = read_board(text, check.messages, check.accepted)
    assert [g.decl for g in board.goals] == ["demo", "demo", "demo_b"]
    assert [g.line for g in board.goals] == [5, 6, 9]
    assert board.goals[1].text == "k : True\n⊢ demo" and board.goals[2].text == "⊢ demo_b"


def test_a_reply_is_read_as_proofs_of_what_it_names():
    board = Board(TWO, [Goal(4, "  ", "demo", "⊢ demo"), Goal(7, "  ", "demo_b", "⊢ demo_b")])
    at = board.goals[0]
    assert [e.kind for e in interpret("```lean\nexact key\n```", board, at, ("demo",))] == ["step"]
    routed = interpret("theorem demo_b : True := by\n  exact key", board, at, ("demo",))
    assert [(e.kind, e.name, e.body) for e in routed] == [("prove", "demo_b", "exact key")]
    new = interpret("lemma helper (n : ℕ) :\n    n = n := by\n  rfl", board, at, ("demo",))
    assert new[0].kind == "hoist" and new[0].name == "helper" and new[0].body == "rfl"
    assert new[0].block.endswith(":= by\n  sorry")
    closed = Board(TWO.replace("theorem demo : True := by\n  sorry", "theorem demo : True := by\n  trivial"),
                   [Goal(7, "  ", "demo_b", "⊢ demo_b")])
    assert [e.kind for e in interpret("theorem demo : True := by\n  trivial",
                                      closed, closed.goals[0], ("demo",))] == ["drop"]


def test_two_models_work_two_goals_and_the_file_is_finished():
    # The shared-lemma question comes first and takes one reply from each line.
    result, lean, llm, _ = run(TWO, {
        "model-a": ["no", "have key : True := by trivial", "exact key"],
        "model-b": ["no", "have key : True := by trivial", "exact key"],
    })
    assert result.metadata["accepted_by_repl"] is True
    assert "sorry" not in result.solution
    assert {e["by"] for e in steps(result) if e["accepted"]} == {"model-a", "model-b"}


def test_a_slow_model_does_not_hold_the_fast_one_up():
    result, lean, llm, wall = run(TWO, {
        "model-a": ["no", "have key : True := by trivial", "exact key",
                    "have key : True := by trivial", "exact key"],
        "model-b": ["no", "have key : True := by trivial"],
    }, delay={"model-b": 0.6})
    assert result.metadata["accepted_by_repl"] is True
    # model-a's four turns did not wait behind model-b's 0.6s reply.
    assert wall < 1.5, wall


def test_a_whole_proof_of_another_open_declaration_replaces_its_body():
    result, lean, llm, _ = run(TWO, {
        "model-a": ["no", "no",
                    "theorem demo_b : True := by\n  have key : True := by trivial\n  exact key",
                    "have key : True := by trivial", "exact key"],
    }, lines=("model-a",))
    assert {"kind": "route", "by": "model-a", "to": "demo_b"} in result.metadata["events"]
    assert result.metadata["accepted_by_repl"] is True


def test_a_step_that_leaves_the_goal_exactly_as_it_was_is_refused():
    result, lean, llm, _ = run(ONE, {"model-a": ["norm_num", "have key : True := by trivial",
                                                 "exact key"]}, lines=("model-a",))
    first = steps(result)[0]
    assert first["accepted"] is False
    assert any("exactly as it was" in p for _, p in llm.calls)
    assert result.metadata["accepted_by_repl"] is True


def test_a_reply_about_a_goal_the_other_model_already_closed_is_stale():
    result, lean, llm, _ = run(ONE, {
        "model-a": ["have key : True := by trivial", "exact key"],
        "model-b": ["have key : True := by trivial"],
    }, delay={"model-b": 0.5})
    assert result.metadata["accepted_by_repl"] is True
    kinds = [e.get("kind") for e in result.metadata["events"]]
    assert "stale" in kinds or "sorry" not in result.solution


def test_a_rejected_prefix_keeps_the_lines_that_were_right():
    result, lean, llm, _ = run(ONE, {"model-a": ["have key : True := by trivial\nlinarith",
                                                 "exact key"]}, lines=("model-a",))
    assert any(e.get("kind") == "prefix" for e in result.metadata["events"])
    assert result.metadata["accepted_by_repl"] is True


def test_the_graded_entry_point_can_be_the_board():
    from submission.board_agent import create_agent
    assert isinstance(create_agent(), BoardAgent)
