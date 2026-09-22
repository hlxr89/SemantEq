import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ∃ (E : Set ℝ) (f : ℝ → ℝ), ContinuousOn f E ∧ ¬∃ g : ℝ → ℝ, Continuous g ∧ ∀ x ∈ E, g x = f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  rcases dummy_assumed with ⟨E, f, hf, hno⟩
  refine ⟨E, f, hf, ?_⟩
  rintro ⟨g, hg, hagree⟩
  exact hno ⟨g, hg, fun x hx => (hagree x hx).symm⟩
