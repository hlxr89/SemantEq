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
  have hf : ContinuousOn (fun _ : ℝ => (0 : ℝ)) Set.univ := continuous_const.continuousOn
  obtain ⟨F, g, hg, hFE, hagree, hno⟩ :=
    dummy_assumed ℝ Set.univ (fun _ => (0 : ℝ)) hf
  refine ⟨Set.univ, (fun _ => (0 : ℝ)), hf, ?_⟩
  intro hext
  apply hno
  obtain ⟨g', hg', hagree'⟩ := hext
  exact ⟨g', hg', fun x hx => (hagree' x hx).symm⟩
