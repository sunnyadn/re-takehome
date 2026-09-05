import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib

attribute [instance 2000] instPowNat

theorem vm_cell_200 (vm_p1 : ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ (10 : ℕ) = a * b) (h2_5_coprime : Nat.Coprime (2 : ℕ) (5 : ℕ)) : ∀ (n : ℕ), (∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b) → (10 : ℕ) ≤ n := by
  intro n hn
  rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
  have h2dvd : (2 : ℕ) ∣ a ^ 2 * b ^ 5 := by
    have : (2 : ℕ) ∣ (2000 : ℕ) := by norm_num
    exact Nat.dvd_trans this hdiv
  have h5dvd : (5 : ℕ) ∣ a ^ 2 * b ^ 5 := by
    have : (5 : ℕ) ∣ (2000 : ℕ) := by norm_num
    exact Nat.dvd_trans this hdiv
  have h2ab : (2 : ℕ) ∣ a * b := by
    rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 2)).mp h2dvd with h2a | h2b
    · exact dvd_mul_of_dvd_left (Nat.Prime.dvd_of_dvd_pow (by decide) h2a) b
    · exact dvd_mul_of_dvd_right (Nat.Prime.dvd_of_dvd_pow (by decide) h2b) a
  have h5ab : (5 : ℕ) ∣ a * b := by
    rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp h5dvd with h5a | h5b
    · exact dvd_mul_of_dvd_left (Nat.Prime.dvd_of_dvd_pow (by decide) h5a) b
    · exact dvd_mul_of_dvd_right (Nat.Prime.dvd_of_dvd_pow (by decide) h5b) a
  have h10dvd : (10 : ℕ) ∣ a * b :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd h2_5_coprime h2ab h5ab
  have hab_pos : 0 < a * b := mul_pos ha hb
  exact Nat.le_of_dvd hab_pos h10dvd

theorem vm_cell_193 (vm_p1 : (∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ (10 : ℕ) = a * b)) : ∀ (n : ℕ), (∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b) → (10 : ℕ) ≤ n := by
  have h2_5_coprime : Nat.Coprime 2 5 := by decide
  first | (exact vm_cell_200 ‹_› ‹_›) | (exact vm_cell_200 vm_p1 h2_5_coprime) | (apply vm_cell_200 <;> assumption)

theorem vm_cell_190 : ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ (10 : ℕ) = a * b := by
  exact ⟨1, 10, by norm_num⟩

theorem h_min : IsLeast {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10 := by
  have h_witness : ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ 10 = a * b := by
    exact vm_cell_190
  have h_min : ∀ n, (∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b) → 10 ≤ n := by
    first | (exact vm_cell_193 ‹_›) | (exact vm_cell_193 vm_p1) | (apply vm_cell_193 <;> assumption)
  exact ⟨h_witness, h_min⟩

theorem vm_cell_179 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2ab : (2 : ℕ) ∣ a * b) (h5prime : Nat.Prime (5 : ℕ)) (h5dvdprod : (5 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5a_or_b : (5 : ℕ) ∣ a ∨ (5 : ℕ) ∣ b) (h5a : (5 : ℕ) ∣ a → (10 : ℕ) ≤ a * b) (h5b : (5 : ℕ) ∣ b → (10 : ℕ) ≤ a * b) : (10 : ℕ) ≤ a * b := by
  first
  | (trace "closer 0"; rfl; done)
  | (trace "closer 1"; trivial; done)
  | (trace "closer 2"; assumption; done)
  | (trace "closer 3"; norm_num; done)
  | (trace "closer 4"; simp; done)
  | (trace "closer 5"; omega; done)
  | (trace "closer 6"; positivity; done)
  | (trace "closer 7"; ring; done)
  | (trace "closer 8"; linarith; done)
  | (trace "closer 9"; nlinarith; done)
  | (trace "closer 10"; field_simp; ring; done)
  | (trace "closer 11"; simp; omega; done)
  | (trace "closer 12"; norm_num; omega; done)
  | (trace "closer 13"; constructor <;> norm_num; done)
  | (trace "closer 14"; simp_all; done)
  | (trace "closer 15"; aesop; done)
  | (trace "closer 16"; decide; done)
  | (trace "closer 17"; gcongr; done)
  | (trace "closer 18"; bound; done)
  | (trace "closer 19"; norm_cast; done)
  | (trace "closer 20"; push_cast; ring; done)
  | (trace "closer 21"; interval_cases <;> norm_num; done)
  | (trace "closer 22"; exact le_refl _; done)
  | (trace "closer 23"; tauto; done)
  | (trace "closer 24"; subst_vars <;> omega; done)
  | (trace "closer 25"; subst_vars <;> ring; done)
  | (trace "closer 26"; subst_vars <;> nlinarith; done)
  | (trace "closer 27"; constructor <;> omega; done)
  | (trace "closer 28"; refine ⟨?_, ?_⟩ <;> norm_num; done)
  | (trace "closer 29"; simp_all <;> omega; done)
  | (trace "closer 30"; zify; omega; done)
  | (trace "closer 31"; push_cast; omega; done)
  | (trace "closer 32"; ring_nf; omega; done)
  | (trace "closer 33"; ring_nf; nlinarith; done)
  | (trace "closer 34"; interval_cases <;> omega; done)
  | (trace "closer 35"; simp_arith; done)
  | (trace "closer 36"; constructor <;> simp; done)
  | (trace "closer 37"; refine ⟨?_, ?_, ?_⟩ <;> norm_num; done)
  | (trace "closer 38"; decide <;> norm_num; done)
  | (trace "closer 39"; field_simp; nlinarith; done)
  | (trace "closer 40"; rify; nlinarith; done)
  | (trace "closer 41"; omega <;> norm_num; done)

theorem vm_cell_180 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2ab : (2 : ℕ) ∣ a * b) (h5prime : Nat.Prime (5 : ℕ)) (h5dvdprod : (5 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5a_or_b : (5 : ℕ) ∣ a ∨ (5 : ℕ) ∣ b) (h5a : (5 : ℕ) ∣ a → (10 : ℕ) ≤ a * b) : (5 : ℕ) ∣ b → (10 : ℕ) ≤ a * b := by
  have h5b : 5 ∣ b → 10 ≤ a * b := by
    intro h5b
    have h2ab' : 2 ∣ a * b := h2ab
    have h5b' : 5 ∣ b := h5b
    have h5dva : 5 ∣ a * b := dvd_mul_of_dvd_right h5b' a
    have h10dva : 10 ∣ a * b := by
      have h2_5_coprime : Nat.Coprime 2 5 := by decide
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h2_5_coprime h2ab' h5dva
    have ha_pos : 0 < a * b := mul_pos ha hb
    exact Nat.le_of_dvd ha_pos h10dva

  exact h5b

theorem vm_cell_173 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2ab : (2 : ℕ) ∣ a * b) (h5prime : Nat.Prime (5 : ℕ)) (h5dvdprod : (5 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5a_or_b : (5 : ℕ) ∣ a ∨ (5 : ℕ) ∣ b) : (5 : ℕ) ∣ a → (10 : ℕ) ≤ a * b := by
  intro h5a
  have h2ab' : 2 ∣ a * b := h2ab
  have h5a' : 5 ∣ a := h5a
  have h5b' : 5 ∣ a * b := dvd_mul_of_dvd_left h5a' b
  have h10dva : 10 ∣ a * b := by
    have h2dva : 2 ∣ a * b := h2ab'
    have h5dva : 5 ∣ a * b := h5b'
    have h2_5_coprime : Nat.Coprime 2 5 := by decide
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h2_5_coprime h2dva h5dva
  have ha_pos : 0 < a * b := mul_pos ha hb
  have h10_le_ab : 10 ≤ a * b := Nat.le_of_dvd ha_pos h10dva
  exact h10_le_ab

theorem vm_cell_171 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2ab : (2 : ℕ) ∣ a * b) (h5prime : Nat.Prime (5 : ℕ)) (h5dvdprod : (5 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5a_or_b : (5 : ℕ) ∣ a ∨ (5 : ℕ) ∣ b) : (10 : ℕ) ≤ a * b := by
  have h5a : 5 ∣ a → 10 ≤ a * b := by
    first | (exact vm_cell_173 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_173 vm_p1 a b ha hb hdiv h2 h5 h2ab h5prime h5dvdprod h5a_or_b) | (apply vm_cell_173 <;> assumption)
  have h5b : 5 ∣ b → 10 ≤ a * b := by
    first | (exact vm_cell_180 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_180 vm_p1 a b ha hb hdiv h2 h5 h2ab h5prime h5dvdprod h5a_or_b h5a) | (apply vm_cell_180 <;> assumption)
  first | (exact vm_cell_179 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_179 vm_p1 a b ha hb hdiv h2 h5 h2ab h5prime h5dvdprod h5a_or_b h5a h5b) | (apply vm_cell_179 <;> assumption)

theorem vm_cell_166 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2ab : (2 : ℕ) ∣ a * b) (h5prime : Nat.Prime (5 : ℕ)) (h5dvdprod : (5 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) : (10 : ℕ) ≤ a * b := by
  have h5a_or_b : 5 ∣ a ∨ 5 ∣ b := by
    have h5dvdprod' : 5 ∣ a ^ 3 * b ^ 4 := h5dvdprod
    have h5prime' : Nat.Prime 5 := h5prime
    have h5a3_or_b4 : 5 ∣ a ^ 3 ∨ 5 ∣ b ^ 4 := (Nat.Prime.dvd_mul h5prime').mp h5dvdprod'
    cases h5a3_or_b4 with
    | inl h =>
      left
      exact Nat.Prime.dvd_of_dvd_pow h5prime' h
    | inr h =>
      right
      exact Nat.Prime.dvd_of_dvd_pow h5prime' h
  first | (exact vm_cell_171 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_171 vm_p1 a b ha hb hdiv h2 h5 h2ab h5prime h5dvdprod h5a_or_b) | (apply vm_cell_171 <;> assumption)

theorem vm_cell_134 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2ab : (2 : ℕ) ∣ a * b) (h5prime : Nat.Prime (5 : ℕ)) : (5 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) := by
  first
  | (trace "closer 0"; rfl; done)
  | (trace "closer 1"; trivial; done)
  | (trace "closer 2"; assumption; done)
  | (trace "closer 3"; norm_num; done)
  | (trace "closer 4"; simp; done)
  | (trace "closer 5"; omega; done)
  | (trace "closer 6"; positivity; done)
  | (trace "closer 7"; ring; done)
  | (trace "closer 8"; linarith; done)
  | (trace "closer 9"; nlinarith; done)
  | (trace "closer 10"; field_simp; ring; done)
  | (trace "closer 11"; simp; omega; done)
  | (trace "closer 12"; norm_num; omega; done)
  | (trace "closer 13"; constructor <;> norm_num; done)
  | (trace "closer 14"; simp_all; done)
  | (trace "closer 15"; aesop; done)
  | (trace "closer 16"; decide; done)
  | (trace "closer 17"; gcongr; done)
  | (trace "closer 18"; bound; done)
  | (trace "closer 19"; norm_cast; done)
  | (trace "closer 20"; push_cast; ring; done)
  | (trace "closer 21"; interval_cases <;> norm_num; done)
  | (trace "closer 22"; exact le_refl _; done)
  | (trace "closer 23"; tauto; done)
  | (trace "closer 24"; subst_vars <;> omega; done)
  | (trace "closer 25"; subst_vars <;> ring; done)
  | (trace "closer 26"; subst_vars <;> nlinarith; done)
  | (trace "closer 27"; constructor <;> omega; done)
  | (trace "closer 28"; refine ⟨?_, ?_⟩ <;> norm_num; done)
  | (trace "closer 29"; simp_all <;> omega; done)
  | (trace "closer 30"; zify; omega; done)
  | (trace "closer 31"; push_cast; omega; done)
  | (trace "closer 32"; ring_nf; omega; done)
  | (trace "closer 33"; ring_nf; nlinarith; done)
  | (trace "closer 34"; interval_cases <;> omega; done)
  | (trace "closer 35"; simp_arith; done)
  | (trace "closer 36"; constructor <;> simp; done)
  | (trace "closer 37"; refine ⟨?_, ?_, ?_⟩ <;> norm_num; done)
  | (trace "closer 38"; decide <;> norm_num; done)
  | (trace "closer 39"; field_simp; nlinarith; done)
  | (trace "closer 40"; rify; nlinarith; done)
  | (trace "closer 41"; omega <;> norm_num; done)

theorem vm_cell_133 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2ab : (2 : ℕ) ∣ a * b) : Nat.Prime (5 : ℕ) := by
  first
  | (trace "closer 0"; rfl; done)
  | (trace "closer 1"; trivial; done)
  | (trace "closer 2"; assumption; done)
  | (trace "closer 3"; norm_num; done)
  | (trace "closer 4"; simp; done)
  | (trace "closer 5"; omega; done)
  | (trace "closer 6"; positivity; done)
  | (trace "closer 7"; ring; done)
  | (trace "closer 8"; linarith; done)
  | (trace "closer 9"; nlinarith; done)
  | (trace "closer 10"; field_simp; ring; done)
  | (trace "closer 11"; simp; omega; done)
  | (trace "closer 12"; norm_num; omega; done)
  | (trace "closer 13"; constructor <;> norm_num; done)
  | (trace "closer 14"; simp_all; done)
  | (trace "closer 15"; aesop; done)
  | (trace "closer 16"; decide; done)
  | (trace "closer 17"; gcongr; done)
  | (trace "closer 18"; bound; done)
  | (trace "closer 19"; norm_cast; done)
  | (trace "closer 20"; push_cast; ring; done)
  | (trace "closer 21"; interval_cases <;> norm_num; done)
  | (trace "closer 22"; exact le_refl _; done)
  | (trace "closer 23"; tauto; done)
  | (trace "closer 24"; subst_vars <;> omega; done)
  | (trace "closer 25"; subst_vars <;> ring; done)
  | (trace "closer 26"; subst_vars <;> nlinarith; done)
  | (trace "closer 27"; constructor <;> omega; done)
  | (trace "closer 28"; refine ⟨?_, ?_⟩ <;> norm_num; done)
  | (trace "closer 29"; simp_all <;> omega; done)
  | (trace "closer 30"; zify; omega; done)
  | (trace "closer 31"; push_cast; omega; done)
  | (trace "closer 32"; ring_nf; omega; done)
  | (trace "closer 33"; ring_nf; nlinarith; done)
  | (trace "closer 34"; interval_cases <;> omega; done)
  | (trace "closer 35"; simp_arith; done)
  | (trace "closer 36"; constructor <;> simp; done)
  | (trace "closer 37"; refine ⟨?_, ?_, ?_⟩ <;> norm_num; done)
  | (trace "closer 38"; decide <;> norm_num; done)
  | (trace "closer 39"; field_simp; nlinarith; done)
  | (trace "closer 40"; rify; nlinarith; done)
  | (trace "closer 41"; omega <;> norm_num; done)

theorem vm_cell_161 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2' : (2 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2prime : Nat.Prime (2 : ℕ)) : (2 : ℕ) ∣ a * b := by
  have h2dva_or_b : 2 ∣ a ∨ 2 ∣ b := by
    have h2dvdprod : 2 ∣ a ^ 3 * b ^ 4 := by
      exact h2'
    have h2dva : 2 ∣ a ^ 3 → 2 ∣ a := by
      intro h
      exact Nat.Prime.dvd_of_dvd_pow h2prime h
    have h2db : 2 ∣ b ^ 4 → 2 ∣ b := by
      intro h
      exact Nat.Prime.dvd_of_dvd_pow h2prime h
    have h2a_or_b : 2 ∣ a ∨ 2 ∣ b := by
      have h2ab : 2 ∣ a ^ 3 * b ^ 4 := h2dvdprod
      have h2a3 : 2 ∣ a ^ 3 ∨ 2 ∣ b ^ 4 := (Nat.Prime.dvd_mul h2prime).mp h2ab
      cases h2a3 with
      | inl h =>
        left
        exact h2dva h
      | inr h =>
        right
        exact h2db h
    exact h2a_or_b

  have h2dva : 2 ∣ a → 2 ∣ a * b := by
    intro h
    exact dvd_mul_of_dvd_left h b

  have h2db : 2 ∣ b → 2 ∣ a * b := by
    intro h
    exact dvd_mul_of_dvd_right h a

  have h2ab : 2 ∣ a * b := by
    cases h2dva_or_b with
    | inl h =>
      exact h2dva h
    | inr h =>
      exact h2db h

  exact h2ab

theorem vm_cell_128 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2' : (2 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) : (2 : ℕ) ∣ a * b := by
  have h2prime : Nat.Prime 2 := by decide
  first | (exact vm_cell_161 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_161 vm_p1 a b ha hb hdiv h2 h5 h2' h2prime) | (apply vm_cell_161 <;> assumption)

theorem vm_cell_100 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) : (2 : ℕ) ∣ a * b := by
  have h2' : (2 : ℕ) ∣ a ^ 3 * b ^ 4 := by
    exact Nat.dvd_of_pow_dvd (by decide) h2
  first | (exact vm_cell_128 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_128 vm_p1 a b ha hb hdiv h2 h5 h2') | (apply vm_cell_128 <;> assumption)

theorem vm_cell_74 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) (a b : ℕ) (ha : (0 : ℕ) < a) (hb : (0 : ℕ) < b) (hdiv : (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h2 : (2 : ℕ) ^ (4 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) (h5 : (5 : ℕ) ^ (3 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ)) : (10 : ℕ) ≤ a * b := by
  have h2ab : 2 ∣ a * b := by
    first | (exact vm_cell_100 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_100 vm_p1 a b ha hb hdiv h2 h5) | (apply vm_cell_100 <;> assumption)
  have h5prime : Nat.Prime 5 := by
    first | (exact vm_cell_133 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_133 vm_p1 a b ha hb hdiv h2 h5 h2ab) | (apply vm_cell_133 <;> assumption)
  have h5dvdprod : 5 ∣ a ^ 3 * b ^ 4 := by
    first | (exact vm_cell_134 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_134 vm_p1 a b ha hb hdiv h2 h5 h2ab h5prime) | (apply vm_cell_134 <;> assumption)
  first | (exact vm_cell_166 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_166 vm_p1 a b ha hb hdiv h2 h5 h2ab h5prime h5dvdprod) | (apply vm_cell_166 <;> assumption)

theorem vm_cell_63 (vm_p1 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}) : ∀ n ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b}, (10 : ℕ) ≤ n := by
  intro n hn
  rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
  have h2 : 2 ^ 4 ∣ a ^ 3 * b ^ 4 := by
    have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
    rw [this] at hdiv
    exact Nat.dvd_trans (by simp [Nat.pow_mul, Nat.mul_assoc]) hdiv
  have h5 : 5 ^ 3 ∣ a ^ 3 * b ^ 4 := by
    have : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by norm_num
    rw [this] at hdiv
    exact Nat.dvd_trans (by simp [Nat.pow_mul, Nat.mul_assoc]) hdiv
  first | (exact vm_cell_74 ‹_› a b ‹_› ‹_› ‹_› ‹_› ‹_›) | (exact vm_cell_74 vm_p1 a b ha hb hdiv h2 h5) | (apply vm_cell_74 <;> assumption)

theorem vm_cell_61 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} := by
  exact ⟨5, 2, by norm_num, by norm_num⟩

theorem vm_cell_51 : IsLeast {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} (10 : ℕ) := by
  have h_witness : 10 ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} := by
    exact vm_cell_61
  have h_min : ∀ n ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b}, 10 ≤ n := by
    first | (exact vm_cell_63 ‹_›) | (exact vm_cell_63 vm_p1) | (apply vm_cell_63 <;> assumption)
  exact ⟨h_witness, h_min⟩

theorem vm_cell_214 (h_witness : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b}) ⦃n : ℕ⦄ (hn : n ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b}) : (10 : ℕ) ≤ n := by
  exact vm_cell_193 h_witness n hn

theorem vm_cell_204 (h_witness : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b}) : IsLeast {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} (10 : ℕ) := by
  refine ⟨h_witness, ?_⟩
  intro n hn
  first | (exact vm_cell_214 ‹_›) | (exact vm_cell_214 h_witness) | (apply vm_cell_214 <;> assumption)

theorem vm_cell_48 (h_witness : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b}) : IsLeast {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} (10 : ℕ) := by
  first | (exact vm_cell_204 ‹_›) | (exact vm_cell_204 h_witness) | (apply vm_cell_204 <;> assumption)

theorem vm_cell_17 : (10 : ℕ) ∈ {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} := by
  exact ⟨1, 10, by norm_num⟩

theorem vm_cell_13 : IsLeast {n | ∃ a b, (0 : ℕ) < a ∧ (0 : ℕ) < b ∧ (2000 : ℕ) ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} (10 : ℕ) := by
  have h_witness : 10 ∈ {n | ∃ a b, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} := by
    exact vm_cell_17
  first | (exact vm_cell_48 ‹_›) | (exact vm_cell_48 h_witness) | (apply vm_cell_48 <;> assumption)

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (2 : ℕ) * b ^ (5 : ℕ) ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ (3 : ℕ) * b ^ (4 : ℕ) ∧ n = a * b} 10) := by
  refine ⟨?_, ?_⟩
  case refine_1 =>
    exact vm_cell_13
  case refine_2 =>
    exact vm_cell_51
