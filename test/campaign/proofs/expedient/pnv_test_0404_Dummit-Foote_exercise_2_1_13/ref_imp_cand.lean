import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_1_13_assumed (H : AddSubgroup ℚ) {x : ℚ}
  (hH : (x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {H : AddSubgroup ℚ} (hH : ∀ x ∈ H, x ≠ 0 → (1 / x) ∈ H) : H = ⊥ ∨ H = ⊤ := by
  exact exercise_2_1_13_assumed H (x := 1) fun h => by simpa using h.1
