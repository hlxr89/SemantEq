import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_4_8a_assumed
  (E : Set ℝ) (f : ℝ → ℝ) (hf : UniformContinuousOn f E)
  (hE : Bornology.IsBounded E) : Bornology.IsBounded (Set.image f E) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {E : Set ℝ} (hE : BddAbove E) (f : ℝ → ℝ) (hf : UniformContinuous f) (hfE : ∀ x ∈ E, f x ∈ E) : BddAbove (f '' E) := by
  exact hE.mono fun _ ⟨x, hx, rfl⟩ ↦ hfE x hx
