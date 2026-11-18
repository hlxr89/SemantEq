import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (h : ∀ (x : ℝ), Tendsto (fun h => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) : ∃ (x₀ : ℝ), ¬ ContinuousAt f x₀ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  -- not proved: the candidate statement is false for the zero function and only implies this goal via contradiction
  sorry
