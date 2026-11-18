import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (X : Type*) [TopologicalSpace X] (E : Set X) (f : X → ℝ) (hf : ContinuousOn f E) : ∃ (F : Set X) (g : X → ℝ), ContinuousOn g F ∧ F ⊆ E ∧ (∀ (x : X), x ∈ F → g x = f x) ∧ ¬ ∃ (g : X → ℝ), Continuous g ∧ ∀ (x : X), x ∈ E → g x = f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  let f : ℝ → ℝ := fun _ => 0
  have hf : ContinuousOn f (∅ : Set ℝ) := continuousOn_const
  obtain ⟨F, g, hg, hFE, hgf, hno⟩ :=
    dummy_assumed ℝ (∅ : Set ℝ) f hf
  refine ⟨∅, f, hf, ?_⟩
  rintro ⟨g', hg', hagree⟩
  apply hno
  refine ⟨g', hg', ?_⟩
  intro x hx
  exact (hagree x hx).symm
