import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {f : ℝ → ℝ} (hf : UniformContinuousOn f (Set.Icc (-4) 4)) : ContinuousOn f (Set.Icc (-4) 4) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_8a
  (E : Set ℝ) (f : ℝ → ℝ) (hf : UniformContinuousOn f E)
  (hE : Bornology.IsBounded E) : Bornology.IsBounded (Set.image f E) := by
  have hEtb : TotallyBounded E :=
    hE.isCompact_closure.totallyBounded.subset subset_closure
  have hu : TotallyBounded (Set.univ : Set E) := by
    rw [← (totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing)]
    simpa using hEtb
  have himage : TotallyBounded ((E.restrict f) '' (Set.univ : Set E)) :=
    hu.image ((uniformContinuousOn_iff_restrict).mp hf)
  have heq : (E.restrict f) '' (Set.univ : Set E) = Set.image f E := by
    ext y
    simp
  rw [heq] at himage
  exact himage.isBounded
