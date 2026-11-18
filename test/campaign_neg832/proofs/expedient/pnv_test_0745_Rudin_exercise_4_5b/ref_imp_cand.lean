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
theorem dummy (E : Set ℝ) (f : ℝ → ℝ) (h : ContinuousOn f E) : ∃ (g : ℝ → ℝ), ContinuousOn g E ∧ ∀ (x : ℝ), g x = f x → (x ∈ E ∨ ¬ ContinuousAt g x) := by
  classical
  let g : ℝ → ℝ := fun x => if x ∈ E then f x else f x + 1
  refine ⟨g, h.congr fun x hx => by simp [g, hx], ?_⟩
  intro x hx
  by_cases hxe : x ∈ E
  · exact Or.inl hxe
  · simp [g, hxe] at hx
