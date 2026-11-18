import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {E : Set ℝ} (hE : E.Nonempty) {f : ℝ → ℝ} (hf : Continuous f): ∃ (hE' : E ⊆ Set.univ), ¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ (x : ℝ), x ∈ E → g x = f x := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  obtain ⟨_, h⟩ := dummy_assumed (E := ({0} : Set ℝ)) (Set.singleton_nonempty 0)
    (f := fun _ => 0) continuous_const
  exfalso
  apply h
  exact ⟨fun _ => 0, continuous_const, by
    intro x hx
    rfl⟩
