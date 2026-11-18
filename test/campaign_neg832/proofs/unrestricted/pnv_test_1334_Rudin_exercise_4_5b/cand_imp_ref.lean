import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (E : Set ℝ) : ∃ (f : ℝ → ℝ)(Hf : ContinuousOn f E), ∀ (g : ℝ → ℝ), g =ᶠ[𝓝ˢ E] f → ¬Continuous g := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5b
  : ∃ (E : Set ℝ) (f : ℝ → ℝ), (ContinuousOn f E) ∧
  (¬ ∃ (g : ℝ → ℝ), Continuous g ∧ ∀ x ∈ E, f x = g x) := by
  rcases dummy_assumed Set.univ with ⟨f, hf, hbad⟩
  exact False.elim (hbad f Filter.EventuallyEq.rfl (continuousOn_univ.mp hf))
