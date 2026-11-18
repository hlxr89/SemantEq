import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : (∃ w : ℂ, w ^ 3 = 1 ∧ w = -1 + 3 * I) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_2 :
  (⟨-1/2, Real.sqrt 3 / 2⟩ : ℂ) ^ 3 = 1 := by
  rcases dummy_assumed with ⟨w, hw, rfl⟩
  norm_num [Complex.ext_iff, pow_succ] at hw
