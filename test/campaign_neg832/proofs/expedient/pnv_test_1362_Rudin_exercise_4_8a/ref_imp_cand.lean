import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_8a_assumed
  (E : Set ℝ) (f : ℝ → ℝ) (hf : UniformContinuousOn f E)
  (hE : Bornology.IsBounded E) : Bornology.IsBounded (Set.image f E) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {f : ℝ → ℝ} {E : Set ℝ} (hEbdd : BddAbove E) (hf_uc : UniformContinuous f) : BddAbove (f '' E) := by
  -- not proved: the statement is false, e.g. f x = -x and E = Set.Iic 0
  sorry
