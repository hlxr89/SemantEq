import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {p : ℕ} [Fact (Nat.Prime p)] (f : Polynomial (ZMod p)) (hf : f.Monic) (hfd : f.degree > 1) (hp : ∀ (x : ℕ), x < p → p ∣ x^p - x) : Irreducible f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_9_4_2a : Irreducible (X^4 - 4*X^3 + 6 : Polynomial ℤ) := by
  have hp : ∀ x : ℕ, x < 2 → 2 ∣ x ^ 2 - x := by
    intro x hx
    interval_cases x <;> simp
  have hirr : Irreducible (X ^ 2 : Polynomial (ZMod 2)) :=
    dummy_assumed (X ^ 2 : Polynomial (ZMod 2)) (by simp) (by simp) hp
  have hnot : ¬ Irreducible (X ^ 2 : Polynomial (ZMod 2)) := by
    exact not_irreducible_pow (by decide)
  exact (hnot hirr).elim
