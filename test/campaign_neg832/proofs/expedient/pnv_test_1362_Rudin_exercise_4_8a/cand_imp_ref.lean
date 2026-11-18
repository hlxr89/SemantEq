import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} {E : Set ℝ} (hEbdd : BddAbove E) (hf_uc : UniformContinuous f) : BddAbove (f '' E) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_8a
  (E : Set ℝ) (f : ℝ → ℝ) (hf : UniformContinuousOn f E)
  (hE : Bornology.IsBounded E) : Bornology.IsBounded (Set.image f E) := by
  have hbad : BddAbove ((fun x : ℝ => -x) '' Set.Iic 0) :=
    dummy_assumed (f := fun x : ℝ => -x) (E := Set.Iic 0) bddAbove_Iic
      (uniformContinuous_id.neg : UniformContinuous (fun x : ℝ => -x))
  rcases hbad with ⟨a, ha⟩
  have hy : |a| + 1 ∈ (fun x : ℝ => -x) '' Set.Iic 0 := by
    refine ⟨-(|a| + 1), ?_, by ring⟩
    change -(|a| + 1) ≤ 0
    linarith [abs_nonneg a]
  have hay := ha hy
  exfalso
  linarith [le_abs_self a]
