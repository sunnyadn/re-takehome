"""Tests for the submission agent's search control, not for the harness."""

from submission.agent import COCKTAIL, Line, sweep_files, wrap_tactic


def _walk(errors, accepted=False):
    line = Line(index=0, owner="m")
    seen = []
    for i, e in enumerate(errors):
        line.candidate, line.errors = f"file-{i}", e
        line.signature, line.feedback = f"sig-{e}", f"fb-{e}"
        line.keep_best(accepted)
        seen.append((line.errors, line.candidate))
    return line, seen


def test_regression_is_rolled_back_to_the_best_file():
    # The trajectory a baseline run actually produced on putnam_2020_a2.
    line, seen = _walk([5, 2, 16, 17, 7, 7])
    assert [e for e, _ in seen] == [5, 2, 2, 2, 2, 2]
    assert all(c == "file-1" for _, c in seen[1:])
    assert line.rejected


def test_monotone_descent_is_never_rolled_back():
    line, seen = _walk([9, 6, 3, 0])
    assert [e for e, _ in seen] == [9, 6, 3, 0]
    assert not line.rejected


def test_an_accepted_file_survives_a_higher_error_count():
    line = Line(index=0, owner="m")
    line.candidate, line.errors = "good", 1
    line.keep_best(False)
    line.candidate, line.errors = "accepted", 3
    assert line.keep_best(True) is False
    assert line.candidate == "accepted"


def test_the_rejection_memo_stays_short_and_deduplicated():
    line, _ = _walk([1, 9, 9, 8, 7, 6])
    assert len(line.rejected) <= 3
    assert len(set(line.rejected)) == len(line.rejected)


def test_every_cocktail_alternative_is_parenthesised():
    # A bare `;` truncates the enclosing `first` block and silently drops the
    # alternatives after it, which once cost the sweep three quarters of its hits.
    for tactic in COCKTAIL:
        assert wrap_tactic(tactic).startswith("(") and wrap_tactic(tactic).endswith("; done)")


def test_sweep_declines_a_file_with_a_sorry_outside_a_proof():
    source = "import Mathlib\n\ndef answer : Nat := sorry\n\ntheorem t : True := by\n  sorry\n"
    assert sweep_files(source) == []
