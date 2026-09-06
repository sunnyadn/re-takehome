from submission.cells import (Cells, CELL_PROBE, all_spans, dissolve, enclosing, marker, reset_cell,
                              modular, remap, render_check, spans, strip_markers)

FILE = """import Mathlib

theorem demo (n : ℕ) (h : 0 < n) : n ≠ 0 := by
  intro hn
  -- cell 1
  have k : n = 0 := by
    -- cell 2
    simp at hn
    sorry
  sorry

theorem demo_b : True := by
  sorry
"""


def cells_for(*stmts):
    cells = Cells()
    for s in stmts:
        cells.new(s)
    return cells


def test_spans_follow_indentation_and_nest():
    tree = spans(FILE)
    assert [(s.id, s.start, s.end, s.indent) for s in tree] == [(1, 5, 10, 2)]
    assert [(s.id, s.start, s.end, s.indent) for s in tree[0].children] == [(2, 7, 9, 4)]
    assert enclosing(FILE, 9).id == 2 and enclosing(FILE, 10).id == 1 and enclosing(FILE, 4) is None
    assert "-- cell" not in strip_markers(FILE) and "-- cell 2" not in dissolve(FILE, 2)
    assert "-- cell 1" in dissolve(FILE, 2)


def test_a_full_render_puts_children_before_parents_and_links_them():
    cells = cells_for("(n : ℕ) (h : 0 < n) (hn : n = 0) : False", "(n : ℕ) (hn : n = 0) : n = 0")
    got = render_check(FILE, cells, focus=None)
    lines = got.text.split("\n")
    c2 = lines.index("theorem vm_cell_2 (n : ℕ) (hn : n = 0) : n = 0 := by")
    c1 = lines.index("theorem vm_cell_1 (n : ℕ) (h : 0 < n) (hn : n = 0) : False := by")
    main = lines.index("theorem demo (n : ℕ) (h : 0 < n) : n ≠ 0 := by")
    assert c2 < c1 < main
    assert lines[c2 + 1:c2 + 3] == ["  simp at hn", "  " + CELL_PROBE]
    assert lines[c1 + 1] == "  have k : n = 0 := by" and lines[c1 + 2] == "    first | (exact vm_cell_2 n ‹_›) | (exact vm_cell_2 n hn) | (apply vm_cell_2 <;> assumption)"
    assert lines[c1 + 3] == "  " + CELL_PROBE
    assert lines[main + 1:main + 3] == ["  intro hn", "  first | (exact vm_cell_1 n ‹_› ‹_›) | (exact vm_cell_1 n h hn) | (apply vm_cell_1 <;> assumption)"]
    assert got.lines[c2] == 7 and got.lines[c2 + 2] == 9 and got.lines[c1 + 2] == 7 and got.lines[main + 2] == 5
    assert "-- cell" not in got.text and got.region is None
    back = remap([{"severity": "error", "pos": {"line": c2 + 3, "column": 2}, "endPos": {"line": c2 + 3, "column": 4}}], got.lines)
    assert back[0]["pos"]["line"] == 9 and back[0]["endPos"]["line"] == 9


def test_a_focused_render_stubs_everything_but_the_cell():
    cells = cells_for("(n : ℕ) (h : 0 < n) (hn : n = 0) : False", "(n : ℕ) (hn : n = 0) : n = 0")
    got = render_check(FILE, cells, focus=2)
    lines = got.text.split("\n")
    assert "  simp at hn" in lines and "  " + CELL_PROBE in lines
    c1 = lines.index("theorem vm_cell_1 (n : ℕ) (h : 0 < n) (hn : n = 0) : False := by")
    assert lines[c1 + 1] == "  sorry"
    main = lines.index("theorem demo (n : ℕ) (h : 0 < n) : n ≠ 0 := by")
    assert lines[main + 1] == "  sorry" and "  intro hn" not in lines
    b = lines.index("theorem demo_b : True := by")
    assert lines[b + 1] == "  sorry"
    assert got.region == (7, 9)
    own = render_check(FILE, cells, focus="demo_b")
    assert own.region == (12, 13) and "  " + CELL_PROBE in own.text.split("\n")
    assert own.text.split("\n")[own.text.split("\n").index("theorem demo (n : ℕ) (h : 0 < n) : n ≠ 0 := by") + 1] == "  sorry"


def test_the_delivered_form_keeps_sorry_and_has_no_probes():
    cells = cells_for("(n : ℕ) (h : 0 < n) (hn : n = 0) : False", "(n : ℕ) (hn : n = 0) : n = 0")
    text = modular(FILE, cells)
    assert "extract_goal" not in text and "-- cell" not in text and text.count("sorry") == 3
    assert marker("  ", 7) == "  -- cell 7"


def test_a_block_that_asks_for_a_budget_gets_it_on_its_own_declaration():
    # Measured on rmo_2001_2: the product leaf needs more than 200000
    # heartbeats with the fuller context (fails at 200000 in 10 s, closes at
    # 400000 in 14 s); a tactic-level set_option never bound anything.
    text = ("import Mathlib\n\ntheorem demo (n : ℕ) (h : 0 < n) : n ≠ 0 := by\n  -- cell 1\n"
            "  set_option maxHeartbeats 400000 in (omega)\n")
    cells = cells_for("(n : ℕ) (h : 0 < n) : n ≠ 0")
    lines = render_check(text, cells, focus=None).text.split("\n")
    at = lines.index("theorem vm_cell_1 (n : ℕ) (h : 0 < n) : n ≠ 0 := by")
    assert lines[at - 1] == "set_option maxHeartbeats 400000 in"
    assert lines[at + 1] == "  set_option maxHeartbeats 400000 in (omega)"


def test_resetting_a_cell_puts_its_goal_back_as_one_placeholder():
    from submission.cells import spans
    cell = spans(FILE)[0].children[0]
    text = reset_cell(FILE, cell)
    assert "-- cell 2" not in text and "simp at hn" not in text
    assert text.split("\n")[6] == "    sorry" and "-- cell 1" in text


def test_a_set_literal_after_a_membership_is_ascribed_from_the_binder_types():
    # Measured on putnam_2018_a1: `(a, b) ∈ {(673, 1358114), …}` loses its
    # `: Set (ℤ × ℤ)` when Lean prints the goal, the cell header then fails
    # (`Insert (ℤ × ℤ) ?m` stuck) and the run re-split the same goal 128 times.
    from submission.board.reply import ascribe_literals
    stmt = "(a b : ℤ) (h : (3 : ℤ) * a > (0 : ℤ)) : (a, b) ∈ {((673 : ℤ), (1358114 : ℤ)), ((674 : ℤ), (340033 : ℤ))}"
    assert ascribe_literals(stmt).endswith(": (a, b) ∈ ({((673 : ℤ), (1358114 : ℤ)), ((674 : ℤ), (340033 : ℤ))} : Set (ℤ × ℤ))")
    assert ascribe_literals("(n : ℕ) : n ∈ {(1 : ℕ), (2 : ℕ)} ∨ (4 : ℕ) ≤ n") == "(n : ℕ) : n ∈ ({(1 : ℕ), (2 : ℕ)} : Set ℕ) ∨ (4 : ℕ) ≤ n"
    same = "(S : Set ℕ) (hS : S = {n | (3 : ℕ) ∣ n}) : (6 : ℕ) ∈ S"
    assert ascribe_literals(same) == same


def test_a_cell_is_called_with_data_by_name_and_hypotheses_by_type():
    # Measured in the image: with `hb : 0 < b` the most recent hypothesis and a
    # conclusion that fixes neither variable, `apply … <;> assumption` set
    # `?a := b`; `exact … a b ‹_› ‹_›` cannot, and the by-name and
    # apply forms stay as fallbacks for renamed and inaccessible names.
    from submission.cells import link
    got = link(7, "(a b : ℕ) (ha : (0 : ℕ) < a) (hdiv : (2000 : ℕ) ∣ a ^ (2 : ℕ)) : (10 : ℕ) ≤ a * b")
    assert got == ("first | (exact vm_cell_7 a b ‹_› ‹_›) | (exact vm_cell_7 a b ha hdiv) "
                   "| (apply vm_cell_7 <;> assumption)")
    assert link(8, "(x : ℕ → ℝ) (hpos : ∀ (n : ℕ), (0 : ℝ) < x n) (S : Set ℕ) : True").startswith(
        "first | (exact vm_cell_8 x ‹_› S)")
    assert link(9, ": IsGreatest {n | n < (3 : ℕ)} (2 : ℕ)") == "exact vm_cell_9"


def test_a_lost_goal_reported_at_a_cell_s_link_is_reopened_after_the_cell_not_inside_it():
    # Measured on rmo_2000_6 (frame127 dump 0148-0153): `refine ⟨?_, ?_⟩` left
    # `case refine_2` with no placeholder; its span ended on cell 63's link,
    # which maps back to the marker line, so the placeholder went inside the
    # cell and the leaf that had just closed the cell was refused for it.
    from submission.cells import reopen_past_cell
    text = ("theorem demo : A ∧ B := by\n  refine ⟨?_, ?_⟩\n  -- cell 63\n  have h : A := by\n"
            "    trivial\n  exact h\n\ntheorem other : True := by\n  trivial\n")
    got = reopen_past_cell(text, 3, 4)
    lines = got.split("\n")
    assert lines[:7] == ["theorem demo : A ∧ B := by", "  refine ⟨?_, ?_⟩", "  -- cell 63",
                         "  have h : A := by", "    trivial", "  exact h", "  sorry"]
    # Not a marker line: the plain reopen.
    plain = reopen_past_cell("theorem t : True := by\n  refine ?_\n", 2, 2)
    assert plain.split("\n")[2] == "  sorry"
