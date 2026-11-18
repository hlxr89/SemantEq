import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (a : ℂ) (h : a ^ 3 = 1) : a = ((-1 + √3*i) / 2) ∨ a = ((-1 - √3*i) / 2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_1_2 :
  (⟨-1/2, Real.sqrt 3 / 2⟩ : ℂ) ^ 3 = 1 := by
  obtain h | h := dummy_assumed (i := 0) 1 (by norm_num)
  · have := congrArg Complex.re h
    norm_num at this
  · have := congrArg Complex.re h
    norm_num at this
