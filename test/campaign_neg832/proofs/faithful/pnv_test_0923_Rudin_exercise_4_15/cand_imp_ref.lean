import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (hf : Continuous f) (hf_open : IsOpenMap f) : StrictMono f ∨ StrictAnti f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_15 {f : ℝ → ℝ}
  (hf : Continuous f) (hof : IsOpenMap f) :
  Monotone f := by
  -- not proved: StrictAnti functions allowed by the antecedent need not be Monotone.
  sorry
