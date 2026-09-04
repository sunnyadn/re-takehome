from math import comb

from submission.conjecture import (families, fits, lemma_text, occurrences, read_table,
                                   table_file, verify_file)

LHS = "∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (k + j) j"


def test_occurrences_skip_the_range_bound_and_families_split_the_rest():
    assert len(occurrences(LHS, "k")) == 2
    fam = families(LHS, "k", "n")
    assert "∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (n + j) j" in fam
    assert "∑ j ∈ Finset.Icc 0 k, 2 ^ (n - j) * Nat.choose (k + j) j" in fam
    assert "∑ j ∈ Finset.Icc 0 k, 2 ^ (n - j) * Nat.choose (n + j) j" in fam
    assert len(fam) == 3
    assert occurrences("∑ j ∈ Finset.range (k + 1), f j * k", "k") == [(len("∑ j ∈ Finset.range (k + 1), f j * "), len("∑ j ∈ Finset.range (k + 1), f j * ") + 1)]


def test_the_putnam_family_fits_the_binomial_row_partial_sum_and_nothing_false():
    F = lambda n, k: sum(2 ** (k - j) * comb(n + j, j) for j in range(k + 1))
    table = [[F(n, k) for k in range(7)] for n in range(6)]
    fam = "∑ j ∈ Finset.Icc 0 k, 2 ^ (k - j) * Nat.choose (n + j) j"
    got = fits(table, "n", "k", fam)
    assert "∑ i ∈ Finset.range (k + 1), Nat.choose (n + k + 1) i" in got
    assert all(all(eval_shape(g, n, k) == table[n][k] for n in range(6) for k in range(7)) for g in got)
    wrong = families(LHS, "k", "n")[1]        # exponent generalised, choose not
    F2 = lambda n, k: sum(2 ** max(n - j, 0) * comb(k + j, j) for j in range(k + 1))
    assert fits([[F2(n, k) for k in range(7)] for n in range(6)], "n", "k", wrong) == []


def eval_shape(text, n, k):
    if text.startswith("∑ i ∈ Finset.range (k + 1), Nat.choose (n + k + 1) i"):
        return sum(comb(n + k + 1, i) for i in range(k + 1))
    if text.startswith("2 ^ (n + k + 1) - ∑ i ∈ Finset.range (n + 1), Nat.choose (n + k + 1) i"):
        return 2 ** (n + k + 1) - sum(comb(n + k + 1, i) for i in range(n + 1))
    raise AssertionError(text)


def test_lean_files_and_the_table_reader():
    text = table_file("import Mathlib\n", "n + k", "n", "k", 0)
    assert "def vm_table_0 (n k : ℕ) : ℕ := n + k" in text and "#eval (List.range 6).map" in text
    assert read_table([{"severity": "info", "data": "[[0, 1], [1, 2]]"}]) == [[0, 1], [1, 2]]
    assert read_table([{"severity": "error", "data": "boom"}]) is None
    assert "decide ((n + k) = (k + n))" in verify_file("", "n + k", "k + n", "n", "k")
    assert lemma_text("vm_conj_1", "n", "k", "n + k", "k + n").startswith("theorem vm_conj_1 (n k : ℕ) :\n    n + k = k + n := by\n  sorry")
