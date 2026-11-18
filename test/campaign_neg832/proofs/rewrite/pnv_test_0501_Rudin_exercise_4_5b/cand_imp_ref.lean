import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed : ∃ (s : Set ℝ) (f : ℝ → ℝ), Continuous f ∧ (∀ (x : ℝ), x ∈ s → f x = x) ∧ ¬ ∃ (g : ℝ → ℝ) (hg : Continuous g), ∀ (x : ℝ), x ∈ s → g x = f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  obtain ⟨s, f, hf, _, hno⟩ := dummy_assumed
  refine ⟨s, f, hf.continuousOn, ?_⟩
  intro h
  apply hno
  obtain ⟨g, hg, hagree⟩ := h
  refine ⟨g, hg, ?_⟩
  intro x hx
  exact (hagree x hx).symm
