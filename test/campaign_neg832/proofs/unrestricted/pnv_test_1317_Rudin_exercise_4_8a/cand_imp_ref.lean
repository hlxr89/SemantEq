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
    hE.isCompact_closure.totallyBounded.subset subset_closure
  have hEu : TotallyBounded (Set.univ : Set E) := by
    have hpre : (Subtype.val : E → ℝ) ⁻¹' E = Set.univ := by
      ext x
      simp
    rw [← hpre]
    exact totallyBounded_preimage
      isUniformEmbedding_subtype_val.isUniformInducing hEt
  have him : TotallyBounded ((E.restrict f) '' (Set.univ : Set E)) :=
    hEu.image (uniformContinuousOn_iff_restrict.mp hf)
  have heq : (E.restrict f) '' (Set.univ : Set E) = f '' E := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  rw [heq] at him
  exact him.isBounded
