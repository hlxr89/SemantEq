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
  have hEtb : TotallyBounded E :=
    hE.isCompact_closure.totallyBounded.subset subset_closure
  have hEtb_sub : TotallyBounded (Set.univ : Set E) := by
    rw [← totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing]
    simpa using hEtb
  have himage := hEtb_sub.image ((uniformContinuousOn_iff_restrict).mp hf)
  rw [← Set.range_restrict f E]
  simpa only [Set.image_univ] using himage.isBounded
