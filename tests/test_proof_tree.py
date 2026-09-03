"""The proof tree: goals and tactic blocks alternate, the file is a rendering,
and every undo is `drop` at one goal. Each test is one failure the text board
had on rmo_2000_6 on 2026-09-03."""

from submission.proof_tree import ProofTree

HEADER = "import Mathlib\n\ntheorem demo : P ∧ Q := by\n"


def test_the_file_is_a_rendering_and_lean_goals_map_to_leaves_in_order():
    tree = ProofTree(HEADER, "⊢ P ∧ Q")
    root = tree.root
    [p, q] = tree.expand(root, "constructor", ["⊢ P", "⊢ Q"])
    assert tree.render() == HEADER + "  constructor\n  sorry\n  sorry\n"
    assert [g.text for g in tree.leaves()] == ["⊢ P", "⊢ Q"]
    [p1] = tree.expand(p, "have h1 : R := by\n  sorry\nexact of_r h1", ["⊢ R"])
    assert tree.render() == HEADER + "  constructor\n  have h1 : R := by\n    sorry\n  exact of_r h1\n  sorry\n"
    # Lean prints the open goals in file order: the same order as the leaves
    tree.observe(["h_new : S\n⊢ R", "⊢ Q"])
    assert [g.text for g in tree.leaves()] == ["h_new : S\n⊢ R", "⊢ Q"]
    assert tree.leaves()[0] is p1  # identity survives a changed printed text (v7.53 inherit)


def test_dropping_a_stuck_leaf_keeps_its_proved_siblings():
    # 08:43 win54: `have hmin` held h2a, h5a proved and 2 closed cases; one
    # stuck case took the whole have down.
    tree = ProofTree(HEADER, "⊢ P ∧ Q")
    [p, q] = tree.expand(tree.root, "constructor", ["⊢ P", "⊢ Q"])
    [a, b, rest] = tree.expand(p, "have ha : A := by\n  sorry\nhave hb : B := by\n  sorry\nsorry", ["⊢ A", "⊢ B", "ha : A\nhb : B\n⊢ P"])
    tree.expand(a, "trivial", [])
    tree.expand(b, "trivial", [])
    [stuck] = tree.expand(rest, "rcases k with k | k\ncase inl =>\n  sorry\ncase inr =>\n  exact done", ["case inl\n⊢ P"])
    assert stuck.tries == 0
    tree.drop(stuck)  # the leaf's own attempts go; nothing above it moves
    assert stuck.tactic is None and "trivial" in tree.render() and "rcases k" in tree.render()
    tree.drop(rest)   # one level up: the case split goes, ha and hb stay proved
    r = tree.render()
    assert "rcases k" not in r and r.count("trivial") == 2 and [g.text for g in tree.leaves()] == ["ha : A\nhb : B\n⊢ P", "⊢ Q"]


def test_restart_is_drop_at_the_goal_not_at_the_declaration():
    # 08:51 one55a: one goal left, 6 tries, the declaration went back to its statement.
    tree = ProofTree(HEADER, "⊢ P ∧ Q")
    [p, q] = tree.expand(tree.root, "constructor", ["⊢ P", "⊢ Q"])
    tree.expand(q, "exact q_done", [])
    [leaf] = tree.expand(p, "have h : A := by\n  sorry\nexact of_a h", ["⊢ A"])
    for _ in range(6):
        leaf.tries += 1
    tree.drop(leaf.parent_goal())  # back one level: `have h` goes, Q stays proved
    assert "exact q_done" in tree.render() and "have h" not in tree.render()
    assert [g.text for g in tree.leaves()] == ["⊢ P"]


def test_the_same_goal_is_swept_once_per_node_not_once_per_printed_text():
    # 08:58 one57a: the witness closed `10 ∈ {…}` on one branch; its twin on
    # a sibling branch shared the key, was not swept, and went to a model.
    tree = ProofTree(HEADER, "⊢ P ∧ Q")
    [p, q] = tree.expand(tree.root, "constructor", ["⊢ P", "⊢ Q"])
    [p_a] = tree.expand(p, "refine ?_", ["⊢ P"])   # alternative 1 under P
    tree.drop(p); [p_b] = tree.expand(p, "show P", ["⊢ P"])  # alternative 2, same printed text
    assert p_a is not p_b and p_a.text == p_b.text
    assert tree.leaves() == [p_b, q]
    assert p.history == ["refine ?_"]  # what was tried at this goal, for the planner
