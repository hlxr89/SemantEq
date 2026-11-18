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
theorem dummy {E : Set ℝ} (hE : IsCompact E) (f : ℝ → ℝ) (hf : UniformContinuousOn f E) : ∃ C : ℝ, ∀ x : ℝ, x ∈ E → |f x| ≤ C := by
  have hb := exercise_4_8a_assumed E f hf hE.isBounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  refine ⟨C, fun x hx ↦ ?_⟩
  simpa only [Real.norm_eq_abs] using hC (f x) ⟨x, hx, rfl⟩
