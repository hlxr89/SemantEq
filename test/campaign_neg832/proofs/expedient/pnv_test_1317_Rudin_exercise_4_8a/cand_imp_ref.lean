import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {E : Set ℝ} (hE : BddAbove E) (f : ℝ → ℝ) (hf : UniformContinuous f) (hfE : ∀ x ∈ E, f x ∈ E) : BddAbove (f '' E) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_8a
  (E : Set ℝ) (f : ℝ → ℝ) (hf : UniformContinuousOn f E)
  (hE : Bornology.IsBounded E) : Bornology.IsBounded (Set.image f E) := by
  have hEt : TotallyBounded E :=
    TotallyBounded.subset subset_closure hE.isCompact_closure.totallyBounded
  have hEu : TotallyBounded (Set.univ : Set E) := by
    rw [← totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing]
    simpa only [Set.image_univ, Set.range_subtype_val]
  have hfi : UniformContinuous (E.restrict f) :=
    uniformContinuousOn_iff_restrict.mp hf
  have himg : TotallyBounded ((E.restrict f) '' Set.univ) := hEu.image hfi
  simpa only [Set.image_univ, Set.range_restrict] using himg.isBounded
