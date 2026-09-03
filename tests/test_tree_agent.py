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
            msgs.append({"severity": "error", "pos": {"line": i + 1}, "endPos": {"line": i + 1},
                         "data": f"unsolved goals\n⊢ G{len(msgs)}"})   # file coordinates
    observe(forest, msgs, False)
    assert [g.text for g in forest.leaves()] == ["⊢ G0", "⊢ G1", "⊢ G2"]


class TreeLean:
    """Every `skip` prints a goal named by its line; a `skip` right after
    `constructor` prints two goals; a `skip` right after `exact done` has none."""

    def __init__(self):
        self.sources = []

    async def check_file(self, source, timeout_s=None):
        self.sources.append(source)
        lines, msgs = source.split("\n"), []
        for i, l in enumerate(lines):
            if l.strip() != "skip":
                continue
            prev = lines[i - 1].strip()
            if prev == "exact done":
                msgs.append({"severity": "error", "pos": {"line": i}, "endPos": {"line": i},
                             "data": "no goals to be solved"})
            elif prev.startswith("case ") and prev.endswith("=>"):
                msgs.append({"severity": "error", "pos": {"line": i}, "endPos": {"line": i},
                             "data": f"unsolved goals\n{prev[:-3]}\n⊢ {'A' if prev.split()[1] == 'left' else 'B'}"})
            elif prev == "constructor":
                msgs.append({"severity": "error", "pos": {"line": i}, "endPos": {"line": i},
                             "data": "unsolved goals\ncase left\n⊢ A\n\ncase right\n⊢ B"})
            elif prev.startswith("| rfl"):   # the closers block: never closes anything here
                msgs.append({"severity": "error", "pos": {"line": i - 1}, "endPos": {"line": i - 1},
                             "data": "linarith failed to find a contradiction"})
            elif prev == "exact boom":
                msgs.append({"severity": "error", "pos": {"line": i - 1}, "endPos": {"line": i - 1},
                             "data": "unknown identifier `boom`"})
            else:
                msgs.append({"severity": "error", "pos": {"line": i}, "endPos": {"line": i},
                             "data": f"unsolved goals\n⊢ G{i}"})
        from re_harness.lean import LeanCheck
        errors = [m for m in msgs if "unsolved" not in m["data"] and "no goals" not in m["data"]]
        return LeanCheck(not errors, msgs, "sorry" in source, False, 1)


def test_an_attempt_settles_its_leaves_from_what_lean_prints():
    import asyncio
    from submission.tree_agent import attempt
    forest = forest_from_challenge("import Mathlib\n\ntheorem demo : A ∧ B := by\n  sorry\n")
    [tree] = forest.trees
    from submission.agent import FileCoordinates
    lean = FileCoordinates(TreeLean())
    ok, _ = asyncio.run(attempt(forest, tree, tree.root, "constructor", lean))
    assert ok and [g.text for g in tree.leaves()] == ["case left\n⊢ A", "case right\n⊢ B"]
    assert tree.render().endswith("  constructor\n  case left =>\n    sorry\n  case right =>\n    sorry\n")
    left = tree.leaves()[0]
    ok, _ = asyncio.run(attempt(forest, tree, left, "exact done", lean))
    assert ok and [g.text for g in tree.leaves()] == ["case right\n⊢ B"]   # the spare placeholder went
    assert "case left =>\n    exact done\n  case right =>" in tree.render()
    right = tree.leaves()[0]
    ok, why = asyncio.run(attempt(forest, tree, right, "exact boom", lean))
    assert not ok and right.tactic is None and right.history == ["exact boom"] and "boom" in str(why)
    assert [g.text for g in tree.leaves()] == ["case right\n⊢ B"]


def test_the_tree_agent_proves_a_two_goal_theorem_and_drops_one_level_up_when_a_leaf_keeps_failing():
    import asyncio
    from submission.tree_agent import TreeAgent
    from submission.agent import Config
    from re_harness import Problem
    from tests.test_board_agent import FakeServices, ScriptLLM

    class Lean(TreeLean):
        """`constructor` opens A and B; `exact done` closes; `boom` fails."""
    # A and B alternate (least tries first): 4 failures each drop a leaf's own
    # block (nothing yet), 4 more each drop one level up, the constructor; the
    # root is asked again and closed directly.
    llm = ScriptLLM({"m": ["constructor"] + ["exact boom"] * 16 + ["exact done"]})
    agent = TreeAgent(Config(lines=("m",), budget_usd=1.0, time_limit_s=600.0))
    result = asyncio.run(agent.solve(Problem(id="demo", description="p",
                                             challenge="import Mathlib\n\ntheorem demo : A ∧ B := by\n  sorry\n"),
                                     FakeServices(Lean(), llm)))
    kinds = [e.get("kind") or e.get("stage") for e in result.metadata["events"]]
    assert "drop" in kinds
    assert result.solution.endswith("theorem demo : A ∧ B := by\n  exact done\n")
    assert result.metadata["accepted_by_repl"] is True
