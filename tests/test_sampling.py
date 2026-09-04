from submission.sampling import (SAMPLES, bound_foralls, hypotheses_only, read_sample_hit,
                                 sample_file, sampled_search)

GROUPS = ["(x : ℕ → ℝ)", "(hpos : ∀ (n : ℕ), (0 : ℝ) < x n)", "(hmono : ∀ (n : ℕ), x n ≥ x (n + (1 : ℕ)))",
          "(hsq : ∀ (N : ℕ), ∑ i ∈ Finset.Ico (1 : ℕ) (N + (1 : ℕ)), x (i * i) / ↑i ≤ (1 : ℝ))", "(j : ℕ)"]


def test_a_statement_over_a_sequence_becomes_a_bool_over_samples():
    # Measured in the image: the block claim ∑_{i∈[j²,(j+1)²)} x i / i ≤ (2j+1) x(j²)/j²
    # gets [] (no refutation, hypotheses met) and the false ≤ x(j²)/j gets [[0, 1]].
    names, seq, body = sampled_search(GROUPS, "∑ i ∈ Finset.Ico (j * j) ((j + 1) * (j + 1)), x i / ↑i ≤ x (j * j) / ↑j")
    assert names == ["j"] and seq == "x"
    assert body.startswith("((List.range 12).all fun n => decide ((0 : ℚ) < x n)) && ")
    assert body.endswith("!(decide (∑ i ∈ Finset.Ico (j * j) ((j + 1) * (j + 1)), x i / ↑i ≤ x (j * j) / ↑j))")
    assert "ℝ" not in body
    assert bound_foralls("∀ (N : ℕ), ∀ (M : ℕ), N ≤ M") == "((List.range 12).all fun N => ((List.range 12).all fun M => decide (N ≤ M)))"
    assert hypotheses_only(body).endswith("≤ (1 : ℚ)))")
    text = sample_file("import Mathlib\n", names, seq, body)
    assert "def vm_samples : List (ℕ → ℚ)" in text and "for j in List.range 8 do" in text
    assert text.rstrip().endswith("#eval vm_samples.any fun x => ((List.range 8).any fun j => " + hypotheses_only(body) + ")")
    assert sampled_search(["(f : ℕ → ℕ → ℝ)", "(k : ℕ)"], "f k k = 0") is None
    assert sampled_search(["(x : ℕ → ℝ)", "(k : ℕ)"], "∃ m, x m = 0") is None


def test_the_hit_reader_names_the_sample_and_reports_whether_hypotheses_were_met():
    msgs = [{"severity": "info", "data": "[[0, 1]]"}, {"severity": "info", "data": "true"}]
    assert read_sample_hit(msgs, ["j"]) == (True, {"sequence": SAMPLES[0], "j": "1"})
    assert read_sample_hit([{"severity": "info", "data": "[]"}, {"severity": "info", "data": "true"}], ["j"]) == (True, None)
    assert read_sample_hit([{"severity": "info", "data": "[]"}, {"severity": "info", "data": "false"}], ["j"]) == (False, None)
