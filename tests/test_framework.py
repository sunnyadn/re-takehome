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
    assert fw.cursor_goal(msgs, 4) == "⊢ True"
    # Lean attributes the message to the declaration as often as to the `skip`,
    # so a line that matches nothing still yields the goal that is open.
    assert fw.cursor_goal(msgs, 9) == "⊢ True"
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


def test_a_have_whose_body_names_nothing_known_is_handed_to_search():
    block = ("have h : 2 ^ n % 7 = 1 := Nat.mod_eq_zero_of_dvd h\n"
             "have k : True := by trivial")
    handed = fw.hand_to_search(block)
    assert handed.splitlines()[0].endswith(":= by exact?")
    assert handed.splitlines()[1].endswith(":= by exact?")
    assert fw.UNKNOWN_NAME.search("Unknown identifier `sub_eq`")


def test_the_cheapest_spellings_trim_the_hints_before_the_tactic():
    import submission.framework_agent as fa
    text = "  nlinarith [h1, h2]\n  decide\n"
    forms = fa.lighter_forms(text)
    assert "  nlinarith [h1]\n  decide\n" in forms
    assert "  nlinarith\n  decide\n" in forms
    # A hint list is tried before the tactic is traded down.
    assert forms.index("  nlinarith [h1]\n  decide\n") < forms.index("  linarith [h1, h2]\n  decide\n")


def test_the_cursor_can_be_any_open_goal_not_only_the_first():
    assert len(fw.placeholders(TWO_THEOREMS)) == 2
    source, line = fw.render(TWO_THEOREMS, 1)
    assert line == 7 and source.split("\n")[line - 1].strip() == "skip"
    # The goal being left alone stays `sorry`, so Lean reports one open goal.
    assert source.count("skip") == 1 and source.count("sorry") == 1
    new, span = fw.replace_cursor(TWO_THEOREMS, "trivial", index=1)
    assert span == (7, 8) and new.split("\n")[3].strip() == "sorry"
    assert new.split("\n")[6].strip() == "trivial"
    # An index past the last goal is the last goal, never a crash.
    assert fw.render(TWO_THEOREMS, 9)[1] == 7


def test_a_block_that_restates_the_graded_theorem_is_unwrapped_to_its_body():
    body = "  constructor\n  · intro h\n    trivial\n"
    for head in ("theorem demo (n : ℕ) : n + 0 = n := by\n",
                 "demo (n : ℕ) : n + 0 = n := by\n"):
        assert fw.unwrap_own(head + body, ("demo",)) == "constructor\n· intro h\n  trivial\n"
    # A block that declares something else is left alone.
    other = "theorem helper : True := by trivial"
    assert fw.unwrap_own(other, ("demo",)) == other


TWO_CASES = """case mp
n : ℕ
⊢ 7 ∣ 2 ^ n - 1 → 3 ∣ n

case mpr
n : ℕ
⊢ 3 ∣ n → 7 ∣ 2 ^ n - 1"""


def test_several_goals_behind_one_placeholder_each_get_their_own():
    apart = fw.split_cursor(CHALLENGE, TWO_CASES)
    assert apart.split("\n")[3:7] == ["  case mp =>", "    sorry",
                                      "  case mpr =>", "    sorry"]
    assert len(fw.placeholders(apart)) == 2
    # Lean keeps attributing the message to the declaration, so a second pass
    # over the same text must not split the split.
    assert fw.split_cursor(apart, TWO_CASES) == ""
    # One goal is not a split, and unnamed goals fall back to bullets.
    assert fw.split_cursor(CHALLENGE, "n : ℕ\n⊢ True") == ""
    plain = fw.split_cursor(CHALLENGE, "⊢ True\n\n⊢ False")
    # A bullet keeps its body on the next line, which is where the cursor scans.
    assert plain.split("\n")[3:7] == ["  ·", "    sorry", "  ·", "    sorry"]
    assert len(fw.placeholders(plain)) == 2


# Both messages came off the graded image, checking the file below. Lean counts
# lines from zero, so the bullet is its line 4 and the theorem its line 2.
STRANDED = "import Mathlib\n\ntheorem t : True ∧ True := by\n  constructor\n  · trivial\n  skip\n"
BULLET = {"severity": "error", "pos": {"line": 4, "column": 2},
          "endPos": {"line": 4, "column": 11}, "data": "unsolved goals\ncase mp\n⊢ 3 ∣ n"}
WHOLE = {"severity": "error", "pos": {"line": 2, "column": 62},
         "endPos": {"line": 5, "column": 6}, "data": "unsolved goals\ncase mpr\n⊢ True"}


def test_lean_counts_lines_from_zero_and_this_file_counts_from_one():
    assert fw.message_line(BULLET) == 5 and fw.message_end_line(BULLET) == 5
    assert fw.message_span(WHOLE) == (3, 6)
    assert fw.message_column(BULLET) == 2


def test_the_active_goal_is_the_tightest_span_that_holds_the_cursor():
    # The first message is the branch's, not the cursor's; taking it is what
    # showed the writer `case mp` for six hundred turns while it sat on mpr.
    assert fw.cursor_goal([BULLET, WHOLE], 6) == "case mpr\n⊢ True"
    assert fw.cursor_goal([BULLET, WHOLE], 5) == "case mp\n⊢ 3 ∣ n"


def test_a_goal_no_placeholder_can_reach_is_given_one_inside_its_branch():
    text = STRANDED.replace("  skip\n", "  sorry\n")
    assert fw.unreachable([BULLET, WHOLE], text, 6) == (5, 4)
    reopened = fw.reopen(text, 5, 4)
    assert reopened.split("\n")[5] == "    sorry"
    assert len(fw.placeholders(reopened)) == 2
    # Once it has one, it is not stranded any more.
    assert fw.unreachable([BULLET, WHOLE], reopened, 7) is None


def test_a_search_that_prints_an_option_is_still_an_answer():
    import submission.framework_agent as fa
    # Measured: `#eval (List.range 100).find? p` prints `some 19`, and the same
    # search with `.getD 0` prints `19`.
    said = [{"severity": "info", "data": "some 19"}, {"severity": "info", "data": "19"},
            {"severity": "info", "data": "[1, 2]"}]
    assert fa.printed_numbers(said) == ["19", "19"]


def test_a_reply_that_adds_a_lemma_and_restates_the_theorem_keeps_the_lemma():
    block = ("theorem aux (k : ℕ) : 2 ^ k % 7 = 2 ^ (k % 3) % 7 := by\n"
             "  omega\n\ntheorem demo (n : ℕ) : n + 0 = n := by\n  simp")
    assert fw.drop_own(block, ("demo",)) == (
        "theorem aux (k : ℕ) : 2 ^ k % 7 = 2 ^ (k % 3) % 7 := by\n  omega")
    # A block with no graded name in it is left whole.
    assert fw.drop_own("intro h\nexact h", ("demo",)) == "intro h\nexact h"


def test_a_lemma_whose_proof_fails_keeps_its_statement():
    block = ("theorem aux (k : ℕ) : 2 ^ k % 7 = 2 ^ (k % 3) % 7 := by\n"
             "  simp [Nat.pow_mod]\n  omega")
    assert fw.as_goal(block) == (
        "theorem aux (k : ℕ) : 2 ^ k % 7 = 2 ^ (k % 3) % 7 := by\n  sorry")
    # A term-mode declaration has no proof block to hand back.
    assert fw.as_goal("theorem aux : True := trivial") == ""


HOISTED = """import Mathlib

theorem aux (n : ℕ) : n + 0 = n := by
  sorry

theorem demo (n : ℕ) : n + 0 = n := by
  sorry
"""


def test_the_writer_may_restate_the_declaration_the_cursor_is_inside():
    assert fw.enclosing_name(HOISTED, 0) == "aux"
    assert fw.enclosing_name(HOISTED, 1) == "demo"
    reply = "theorem aux (n : ℕ) : n + 0 = n := by\n  induction n with\n  | zero => simp"
    body = fw.unwrap_own(reply, ("aux",))
    assert body == "induction n with\n| zero => simp"
    # Restating a name that is taken and not the one being proved is not a step.
    assert fw.drop_own(reply, ("aux",)) == ""


def test_a_block_is_cut_back_one_top_level_step_at_a_time():
    block = "intro h\nhave a : True := by\n  trivial\nexact a"
    assert fw.prefixes(block) == ["intro h\nhave a : True := by\n  trivial", "intro h"]
    # A single step has no shorter form worth trying.
    assert fw.prefixes("omega") == []
    assert fw.prefixes("have a : True := by\n  trivial") == []


def test_a_models_thinking_is_not_its_answer():
    import submission.framework_agent as fa
    # Measured on p10: the draft holds ten `#eval` lines that are not the answer.
    reply = "<think>\n#eval 1\n#eval 2\n</think>\n\n#eval 6"
    assert fa.spoken(reply) == "#eval 6"
    # An unclosed think block runs to the end of the reply.
    assert fa.spoken("<think>\nstill going") == ""
    assert fa.spoken("intro h\nexact h") == "intro h\nexact h"


def test_a_tool_call_is_read_when_the_model_makes_one():
    import submission.framework_agent as fa
    calls = [{"function": {"name": "answer",
                           "arguments": '{"evals": ["#eval 6", "#eval 7"]}'}}]
    assert fa.tool_lines(calls) == "#eval 6\n#eval 7"
    # A model that ignores the schema leaves nothing here, and the reply is read.
    assert fa.tool_lines([]) == "" and fa.tool_lines(None) == ""
    assert fa.tool_lines([{"function": {"arguments": "not json"}}]) == ""


SET_SLOT = """import Mathlib

abbrev putnam_solution : Set (ℤ × ℤ) := by
  sorry

theorem putnam (a : ℤ) : (a, a) ∈ putnam_solution := by
  sorry
"""


def test_a_definition_slot_takes_a_term_and_is_not_a_goal():
    assert fw.definition_slots(SET_SLOT) == (("putnam_solution", "Set (ℤ × ℤ)"),)
    filled = fw.fill_definition(SET_SLOT, "putnam_solution", "{p | p.1 = p.2}")
    assert "abbrev putnam_solution : Set (ℤ × ℤ) := {p | p.1 = p.2}" in filled
    assert fw.definition_slots(filled) == ()
    # Once it holds a term the cursor moves on to the theorem below it.
    assert len(fw.placeholders(filled)) == 1
