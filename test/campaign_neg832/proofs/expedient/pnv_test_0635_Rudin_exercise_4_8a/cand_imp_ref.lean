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
  have hEtb : TotallyBounded E :=
    (totallyBounded_Icc (sInf E) (sSup E)).subset hE.subset_Icc_sInf_sSup
  have hsub : TotallyBounded (Set.univ : Set E) := by
    rw [← totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing]
    simpa using hEtb
  have himage := (hsub.image (uniformContinuousOn_iff_restrict.mp hf)).isBounded
  rw [show E.restrict f '' Set.univ = f '' E by ext y; simp [Set.image]] at himage
  exact himage
