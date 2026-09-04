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
    assert lines[c1 + 1] == "  have k : n = 0 := by" and lines[c1 + 2] == "    apply vm_cell_2 <;> assumption"
    assert lines[c1 + 3] == "  " + CELL_PROBE
    assert lines[main + 1:main + 3] == ["  intro hn", "  apply vm_cell_1 <;> assumption"]
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
