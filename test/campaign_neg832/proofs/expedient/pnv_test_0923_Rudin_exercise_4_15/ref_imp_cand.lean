import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_15_assumed {f : ℝ → ℝ}
  (hf : Continuous f) (hof : IsOpenMap f) :
  Monotone f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (f : ℝ → ℝ) (hf : Continuous f) (hf_open : IsOpenMap f) : StrictMono f ∨ StrictAnti f := by
  have h := exercise_4_15_assumed (f := fun x : ℝ => -x) continuous_neg (isOpenMap_neg ℝ)
  have := h (show (0 : ℝ) ≤ 1 by norm_num)
  norm_num at this
