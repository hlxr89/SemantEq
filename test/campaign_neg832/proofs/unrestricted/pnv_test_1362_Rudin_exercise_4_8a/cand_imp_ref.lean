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
    dummy_assumed (f := fun x : ℝ => -x) (E := Set.Iic 0)
      ⟨0, fun _ hx => hx⟩ Real.uniformContinuous_neg
  rcases hbad with ⟨a, ha⟩
  have hx : -(|a| + 1) ∈ Set.Iic (0 : ℝ) := by
    simp only [Set.mem_Iic]
    linarith [abs_nonneg a]
  have himage : |a| + 1 ∈ (fun x : ℝ => -x) '' Set.Iic 0 := by
    refine ⟨-(|a| + 1), hx, ?_⟩
    ring
  have hle : |a| + 1 ≤ a := ha himage
  linarith [le_abs_self a]
