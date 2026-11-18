import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (hf : ∀ (x : ℝ), ∃ (h : ℝ), ∀ (h0 : 0 < h), |f (x + h) - f x| < h) (h : ¬ UniformContinuous f) : ∃ x : ℝ, ContinuousAt f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  -- not proved: any use of the false assumed statement would require an excluded contradiction argument, not semantic transport
  sorry
