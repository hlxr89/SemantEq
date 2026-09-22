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
theorem dummy : ∃ (E : Set ℝ) (f : ℝ → ℝ), ContinuousOn f E ∧ ¬(∃ g : ℝ → ℝ, Continuous g ∧ ∀ x ∈ E, g x = f x) := by
  obtain ⟨E, f, hf, hno⟩ := exercise_4_5b_assumed
  refine ⟨E, f, hf, ?_⟩
  rintro ⟨g, hg, heq⟩
  exact hno ⟨g, hg, fun x hx => (heq x hx).symm⟩
