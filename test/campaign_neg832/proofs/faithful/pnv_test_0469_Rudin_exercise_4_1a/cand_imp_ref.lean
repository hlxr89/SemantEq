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
  let f : ℝ → ℝ := fun _ => 0
  have hf : ∀ (x : ℝ), Tendsto (fun h => f (x + h) - f (x - h)) (𝓝 0) (𝓝 0) := by
    intro x
    simpa [f] using (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝 0) (𝓝 0))
  obtain ⟨x₀, hx₀⟩ := dummy_assumed f hf
  refine ⟨f, ?_, ?_⟩
  · exact hf
  · intro hcont
    exact hx₀ hcont.continuousAt
