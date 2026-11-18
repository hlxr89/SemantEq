import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {E : Set ℝ} (hE : IsCompact E) (f : ℝ → ℝ) (hf : UniformContinuousOn f E) : ∃ C : ℝ, ∀ x : ℝ, x ∈ E → |f x| ≤ C := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_8a
  (E : Set ℝ) (f : ℝ → ℝ) (hf : UniformContinuousOn f E)
  (hE : Bornology.IsBounded E) : Bornology.IsBounded (Set.image f E) := by
  have htot : TotallyBounded E :=
    hE.isCompact_closure.totallyBounded.subset subset_closure
  have htot' : TotallyBounded (Set.univ : Set E) := by
    rw [← totallyBounded_image_iff isUniformEmbedding_subtype_val.isUniformInducing]
    simpa using htot
  have himage := htot'.image (uniformContinuousOn_iff_restrict.mp hf)
  rw [show Set.image f E = Set.range (E.restrict f) by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩]
  rw [Set.image_univ] at himage
  exact himage.isBounded
