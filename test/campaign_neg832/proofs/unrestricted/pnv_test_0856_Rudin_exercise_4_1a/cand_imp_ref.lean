import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : ∀ x : ℝ, Tendsto (fun h => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0)) : ¬Continuous f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  exfalso
  have hz : ∀ x : ℝ,
      Tendsto (fun h : ℝ => (0 : ℝ) - 0) (𝓝 0) (𝓝 0) := by
    intro x
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
  have hnc : ¬ Continuous (fun _ : ℝ => (0 : ℝ)) := by
    apply dummy_assumed
    intro x
    simpa using hz x
  exact hnc continuous_const
