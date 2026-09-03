from submission.tree_agent import forest_from_challenge, observe
from submission.proof_tree import ProofTree

TWO = ("import Mathlib\n\ntheorem demo : True := by\n  sorry\n\n"
       "theorem demo_b (x : ℕ) : x = x := by\n  sorry\n")


def test_a_challenge_becomes_one_tree_per_sorry_declaration_and_renders_back_to_itself():
    forest = forest_from_challenge(TWO)
    assert len(forest.trees) == 2 and forest.render() == TWO
    [a, b] = forest.trees
    a.expand(a.root, "constructor", ["⊢ P", "⊢ Q"])
    assert forest.render() == TWO.replace("theorem demo : True := by\n  sorry\n",
                                          "theorem demo : True := by\n  constructor\n  sorry\n  sorry\n")
    assert len(forest.leaves()) == 3


def test_lean_messages_flow_back_to_the_leaves_in_file_order():
    forest = forest_from_challenge(TWO)
    [a, b] = forest.trees
    a.expand(a.root, "constructor", ["", ""])
    text = forest.render()
    line = text.split("\n")
    # one `unsolved goals` message per placeholder, as the fake and Lean both print
    msgs = []
    for i, l in enumerate(line):
        if l.strip() == "sorry":
            msgs.append({"severity": "error", "pos": {"line": i}, "endPos": {"line": i},
                         "data": f"unsolved goals\n⊢ G{len(msgs)}"})
    observe(forest, msgs, False)
    assert [g.text for g in forest.leaves()] == ["⊢ G0", "⊢ G1", "⊢ G2"]
