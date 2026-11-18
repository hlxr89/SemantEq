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
theorem dummy (h : ∀ x : ℝ, Tendsto (fun h : ℝ => (f (x + h) - f (x - h))) (𝓝 0) (𝓝 0)) : ∃ x, ContinuousAt f x ∧ ¬ ContinuousAt f x := by
  -- not proved: the conclusion is contradictory and does not follow from the unrelated existential antecedent
  sorry
