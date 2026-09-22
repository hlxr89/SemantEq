import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_5b_assumed
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧ (∀ g : ℝ → ℝ, Continuous g → ∃ x ∈ E, f x ≠ g x) := by
  rcases exercise_4_5b_assumed with ⟨E, f, hf, hno⟩
  refine ⟨E, f, hf, ?_⟩
  intro g hg
  by_contra h
  apply hno
  refine ⟨g, hg, ?_⟩
  push_neg at h
  exact h
