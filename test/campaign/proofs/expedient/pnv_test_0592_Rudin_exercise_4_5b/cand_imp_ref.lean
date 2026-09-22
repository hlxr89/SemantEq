import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧ ¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, g x = f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  obtain ⟨E, f, hf, h⟩ := dummy_assumed
  refine ⟨E, f, hf, ?_⟩
  rintro ⟨g, hg, hfg⟩
  exact h ⟨g, hg, fun x hx ↦ (hfg x hx).symm⟩
