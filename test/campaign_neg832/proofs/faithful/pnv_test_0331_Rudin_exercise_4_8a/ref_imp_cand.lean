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
  obtain ⟨C, hC⟩ :=
    (Metric.isBounded_iff_subset_closedBall 0).mp
      (exercise_4_8a_assumed E f hf hE.isBounded)
  refine ⟨C, fun x hx => ?_⟩
  have hx' : f x ∈ Metric.closedBall (0 : ℝ) C := hC ⟨x, hx, rfl⟩
  simpa [Metric.mem_closedBall, Real.dist_eq] using hx'
