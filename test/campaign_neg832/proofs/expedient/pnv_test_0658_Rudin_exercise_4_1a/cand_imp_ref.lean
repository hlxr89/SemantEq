import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (f : ℝ → ℝ) (hf : ∀ x, Tendsto (fun h => f (x + h) - f (x - h)) (𝓝[>] 0) (𝓝 0)) : ∃ x, ¬Tendsto (deriv f) (𝓝 x) (𝓝 (deriv f x)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_1a
  : ∃ (f : ℝ → ℝ), (∀ (x : ℝ), Tendsto (λ y => f (x + y) - f (x - y)) (𝓝 0) (𝓝 0)) ∧ ¬ Continuous f := by
  have hf : ∀ x : ℝ, Tendsto (fun h : ℝ => (0 : ℝ) - 0) (𝓝[>] 0) (𝓝 0) := by
    intro x
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0))
  obtain ⟨x, hx⟩ := dummy_assumed (fun _ : ℝ => 0) hf
  apply (hx ?_).elim
  have hd : deriv (fun _ : ℝ => (0 : ℝ)) = fun _ => 0 := by
    funext y
    exact deriv_const y 0
  rw [hd]
  exact tendsto_const_nhds
