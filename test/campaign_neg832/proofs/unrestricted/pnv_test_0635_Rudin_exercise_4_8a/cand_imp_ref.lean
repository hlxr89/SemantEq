import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {E : Set ℝ} (hE : BddAbove E) {f : ℝ → ℝ} (hf : UniformContinuous f) : BddAbove (f '' E) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_8a
  (E : Set ℝ) (f : ℝ → ℝ) (hf : UniformContinuousOn f E)
  (hE : Bornology.IsBounded E) : Bornology.IsBounded (Set.image f E) := by
  exfalso
  have hb : BddAbove ((fun x : ℝ => -x) '' Set.Iic (0 : ℝ)) :=
    dummy_assumed (E := Set.Iic (0 : ℝ)) ⟨0, by intro x hx; exact hx⟩
      (f := fun x : ℝ => -x) (uniformContinuous_id.neg)
  rcases hb with ⟨a, ha⟩
  let y : ℝ := max a 0 + 1
  have hy_pos : 0 < y := by
    dsimp [y]
    linarith [le_max_right a 0]
  have hy_mem : y ∈ (fun x : ℝ => -x) '' Set.Iic (0 : ℝ) := by
    refine ⟨-y, ?_, by simp⟩
    exact (neg_nonpos.mpr hy_pos.le)
  have hy_le : y ≤ a := ha hy_mem
  dsimp [y] at hy_le
  linarith [le_max_left a 0]
