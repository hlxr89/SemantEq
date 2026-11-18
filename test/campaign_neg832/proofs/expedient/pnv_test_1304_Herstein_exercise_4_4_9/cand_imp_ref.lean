import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} (h_p : p.Prime) : ∃ (r : ℕ), r < p - 1 ∧ (∃ sq : ℕ, sq ^ 2 ≡ r [MOD p]) ∧ (∀ n : ℕ, n < p - 1 - r → ¬∃ sq : ℕ, sq ^ 2 ≡ n [MOD p]) ∧ r = (p - 1) / 2 + (p - 1) / 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_4_9 (p : ℕ) (hp : Nat.Prime p) (hodd : p % 2 = 1) :
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ∃ x : ZMod p, x^2 = q) ∧
  (∃ S : Finset (ZMod p), 0 ∉ S ∧ S.card = (p-1)/2 ∧ ∀ q ∈ S, ¬ ∃ x : ZMod p, x^2 = q) := by
  obtain ⟨r, hr, -, hn, hre⟩ := dummy_assumed hp
  rcases hp.eq_two_or_odd with rfl | hpodd
  · have hzero := hn 0 (by omega)
    exact (hzero ⟨0, by rfl⟩).elim
  · omega
