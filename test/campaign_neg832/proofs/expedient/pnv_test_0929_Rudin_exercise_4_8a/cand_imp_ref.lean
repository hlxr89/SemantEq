import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : UniformContinuous f) (s : Set ℝ) (hs : BddAbove s) : BddAbove (f '' s) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_8a
  (E : Set ℝ) (f : ℝ → ℝ) (hf : UniformContinuousOn f E)
  (hE : Bornology.IsBounded E) : Bornology.IsBounded (Set.image f E) := by
  have hbad : BddAbove ((fun x : ℝ => -x) '' Set.Iic 0) :=
    dummy_assumed (_root_.uniformContinuous_neg) (Set.Iic 0) bddAbove_Iic
  have himage : (fun x : ℝ => -x) '' Set.Iic 0 = Set.Ici 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      refine ⟨-y, ?_, by simp⟩
      simpa using hy
  exact ((not_bddAbove_Ici (0 : ℝ)) (himage ▸ hbad)).elim
