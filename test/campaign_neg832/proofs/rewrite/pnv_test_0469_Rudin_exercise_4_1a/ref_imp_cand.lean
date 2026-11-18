import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_1a_assumed
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (f : ℝ → ℝ) (h : ∀ (x : ℝ), Tendsto (fun h => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) : ∃ (x₀ : ℝ), ¬ ContinuousAt f x₀ := by
  -- not proved: the antecedent concerns one existentially chosen function, not the arbitrary function f
  sorry
