import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (h : ∀ x, Tendsto (fun h => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) : ¬Continuous f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  have hnot : ¬ Continuous (fun _ : ℝ => (0 : ℝ)) := dummy_assumed (f := fun _ : ℝ => (0 : ℝ)) (by
    intro x
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0)))
  exact (hnot continuous_const).elim
