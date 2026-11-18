import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem exercise_4_5b_assumed
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (E : Set ℝ) (f : ℝ → ℝ) (h : ContinuousOn f E) : ∃ (g : ℝ → ℝ), ContinuousOn g E ∧ ∀ (x : ℝ), g x = f x → (x ∈ E ∨ ¬ ContinuousAt g x) := by
  classical
  obtain ⟨E₀, f₀, hf₀, hno⟩ := exercise_4_5b_assumed
  let c : ℝ := if (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E₀, f₀ x = g x) then 1 else 0
  have hc : c = 1 := if_pos hno
  let g : ℝ → ℝ := fun x => if x ∈ E then f x else f x + c
  refine ⟨g, h.congr ?_, ?_⟩
  · intro x hx
    simp [g, hx]
  · intro x hgf
    by_cases hx : x ∈ E
    · exact Or.inl hx
    · exfalso
      simp [g, hx, hc] at hgf

