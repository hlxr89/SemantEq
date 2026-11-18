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
theorem dummy (E : Set ℝ) : ∃ (f : ℝ → ℝ)(Hf : ContinuousOn f E), ∀ (g : ℝ → ℝ), g =ᶠ[𝓝ˢ E] f → ¬Continuous g := by
  -- not proved: the goal is false for E = Set.univ, while the antecedent is satisfiable
  sorry
