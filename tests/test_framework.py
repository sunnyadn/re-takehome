"""The text-cursor model: rendering, editing, and reading Lean's answer."""

from __future__ import annotations

from submission import framework as fw

CHALLENGE = """import Mathlib

theorem demo (n : ℕ) : n + 0 = n := by
  sorry
"""

TWO_THEOREMS = """import Mathlib

theorem a : True := by
  sorry

theorem b : True := by
  sorry
"""

ANSWER_CHALLENGE = """import Mathlib

abbrev p_answer : ℕ := sorry

theorem demo : p_answer = 19 := by
  sorry
"""


def test_cursor_is_the_topmost_placeholder_and_others_stay_sorry():
    source, line = fw.render(TWO_THEOREMS)
    assert source.count("skip") == 1 and source.count("sorry") == 1
    assert source.split("\n")[line - 1].strip() == "skip"
    assert line == 4


def test_answer_slot_is_not_a_placeholder():
    source, line = fw.render(ANSWER_CHALLENGE)
    assert "abbrev p_answer : ℕ := sorry" in source
    assert source.split("\n")[line - 1].strip() == "skip"


def test_replace_cursor_leaves_a_placeholder_for_the_rest():
    new, span = fw.replace_cursor(CHALLENGE, "have h : True := by trivial")
    assert "  have h : True := by trivial" in new
    assert new.rstrip().endswith("sorry")
    assert span == (4, 5)
    assert fw.render(new)[1] == 5


def test_a_closing_step_can_ask_for_no_placeholder():
    new, _ = fw.replace_cursor(CHALLENGE, "simp", trailing=False)
    assert fw.is_done(new)


def test_a_branching_step_keeps_one_placeholder_per_branch():
    step = "induction n with\n| zero => sorry\n| succ k ih => sorry"
    new, span = fw.replace_cursor(CHALLENGE, step, trailing=False)
    assert new.count("sorry") == 2
    assert span == (4, 8)
    source, line = fw.render(new)
    assert source.split("\n")[line - 1].strip() == "skip"
    assert source.count("sorry") == 1


def test_tail_placeholders_are_split_onto_their_own_line():
    block = fw.normalise_steps("have h : True := by sorry")
    assert block.split("\n") == ["have h : True := by", "  sorry"]


def test_model_indentation_is_normalised_to_the_cursor():
    new, _ = fw.replace_cursor(CHALLENGE, "    intro x\n    exact h")
    assert "\n  intro x\n  exact h\n" in new


def test_surplus_placeholder_is_a_message_kind_of_its_own():
    msgs = [
        {"severity": "error", "pos": {"line": 4}, "data": "unsolved goals\n⊢ True"},
        {"severity": "error", "pos": {"line": 5}, "data": "no goals to be solved"},
        {"severity": "error", "data": "(deterministic) timeout at `whnf`, "
                                      "maximum number of heartbeats (200000)"},
        {"severity": "error", "data": "unknown identifier 'foo'"},
        {"severity": "warning", "data": "declaration uses `sorry`"},
    ]
    progress, surplus, expensive, failures = fw.classify(msgs)
    assert len(progress) == len(surplus) == len(expensive) == len(failures) == 1
    assert fw.cursor_goal(msgs, 4) == "True"
    # Lean attributes the message to the declaration as often as to the `skip`,
    # so a line that matches nothing still yields the goal that is open.
    assert fw.cursor_goal(msgs, 9) == "True"
    assert fw.cursor_goal([], 4) == ""


def test_dropping_the_surplus_line_finishes_the_proof():
    new, _ = fw.replace_cursor(CHALLENGE, "simp")
    assert not fw.is_done(new)
    assert fw.is_done(fw.drop_lines(new, [5]))


def test_span_decides_which_step_a_message_belongs_to():
    msg = {"severity": "error", "pos": {"line": 4}, "data": "boom"}
    assert fw.in_span(msg, (4, 5)) and not fw.in_span(msg, (6, 7))
    assert not fw.in_span({"severity": "error", "data": "boom"}, (1, 99))


def test_preamble_goes_under_the_imports():
    text = fw.insert_preamble(CHALLENGE, "#eval 2 + 2")
    lines = text.split("\n")
    assert lines[0].startswith("import") and lines[1] == "#eval 2 + 2"
    assert "theorem demo" in text


def test_answer_slot_is_found_and_filled():
    assert fw.answer_slots(ANSWER_CHALLENGE) == ("p_answer",)
    filled = fw.fill_answer(ANSWER_CHALLENGE, "p_answer", "19")
    assert "abbrev p_answer : ℕ := 19" in filled


def test_sweep_forces_every_alternative_to_close():
    assert fw.sweep_body(("rfl", "omega")).count("; done)") == 2
    assert "any_goals" in fw.any_goals_sweep(("rfl",))
    assert "all_goals" not in fw.any_goals_sweep(("rfl",))


def test_root_names_reads_the_graded_theorems():
    assert fw.root_names(TWO_THEOREMS) == ("a", "b")


SWEPT = """import Mathlib

theorem demo : True := by
  first
  | (rfl; done)
  | (simp; done)
"""


def test_a_search_block_collapses_to_one_alternative():
    blocks = fw.first_blocks(SWEPT)
    assert len(blocks) == 1
    assert fw.alternatives(blocks[0].group(2)) == ["rfl", "simp"]
    collapsed = fw.collapse(SWEPT, blocks[0], "simp")
    assert collapsed.endswith("  simp\n") and "first" not in collapsed


def test_the_axiom_probe_names_every_graded_theorem():
    probed = fw.axiom_probe(CHALLENGE, fw.root_names(CHALLENGE))
    assert probed.rstrip().endswith("#print axioms demo")


def test_lean_s_own_wording_for_no_goals_is_matched_whatever_its_case():
    # Both strings came off the graded image, from the same session.
    left = {"severity": "error", "pos": {"line": 4}, "data": "No goals to be solved"}
    warn = {"severity": "warning", "pos": {"line": 4},
            "data": "'skip' tactic does nothing"}
    progress, surplus, expensive, failures = fw.classify([left, warn])
    assert surplus == [left] and not failures and not progress


def test_a_budget_error_is_not_a_wrong_step():
    # Both lines came off the graded image, checking 7 ^ 2026 % 100 = 49.
    depth = {"severity": "error", "data": "maximum recursion depth has been reached "
             "use `set_option maxRecDepth <num>` to increase limit"}
    threshold = {"severity": "warning", "data": "exponent 2026 exceeds the threshold 256"}
    progress, surplus, expensive, failures = fw.classify([depth, threshold])
    assert expensive == [depth] and not failures


def test_a_goal_with_nowhere_to_work_gets_a_placeholder_back():
    text = "import Mathlib\n\ntheorem t : True ∧ True := by\n  constructor\n  trivial\n"
    # `endPos` is where Lean says the proof block ends.
    reopened = fw.reopen(text, 5)
    assert reopened.split("\n")[5] == "  sorry"
    assert not fw.is_done(reopened) and fw.render(reopened)[1] == 6
