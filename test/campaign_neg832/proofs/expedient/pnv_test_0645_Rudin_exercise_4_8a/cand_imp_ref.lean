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
  have htot : TotallyBounded E :=
    hE.isCompact_closure.totallyBounded.subset subset_closure
  have htot' : TotallyBounded (Set.univ : Set E) := by
    have h := totallyBounded_preimage (isUniformInducing_val E) htot
    exact h.subset (by
      intro x _
      exact x.property)
  have h := (htot'.image (uniformContinuousOn_iff_restrict.mp hf)).isBounded
  rw [show Set.restrict E f '' Set.univ = f '' E by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩] at h
  exact h
