import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {H : AddSubgroup ℚ} (hH : ∀ x ∈ H, x ≠ 0 → 1 / x ∈ H) : H = ⊥ ∨ H = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2_1_13 (H : AddSubgroup ℚ) {x : ℚ}
  (hH : (x ∈ H ∧ x ≠ 0) → (1 / x) ∈ H):
  H = ⊥ ∨ H = ⊤ := by
  -- not proved: closure under inversion at one fixed x does not imply closure at every nonzero member
  sorry
