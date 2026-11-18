import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (h : ∀ x : ℝ, Tendsto (fun h : ℝ => (f (x + h) - f (x - h))) (𝓝 0) (𝓝 0)) : ∃ x, ContinuousAt f x ∧ ¬ ContinuousAt f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  have hconst : ∀ x : ℝ, Tendsto (fun _ : ℝ => (0 : ℕ) - 0) (𝓝 0) (𝓝 0) := by
    intro x
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℕ)) (𝓝 0) (𝓝 0))
  obtain ⟨x, hx, hnx⟩ := dummy_assumed (f := fun _ : ℝ => (0 : ℕ)) hconst
  exact (hnx hx).elim
