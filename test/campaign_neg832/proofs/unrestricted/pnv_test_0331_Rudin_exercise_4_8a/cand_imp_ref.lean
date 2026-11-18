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
  have himage : TotallyBounded (Set.image f E) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨δ, hδ, hcontrol⟩ := (Metric.uniformContinuousOn_iff.mp hf) ε hε
    obtain ⟨t, htE, htfin, hcover⟩ :=
      Metric.finite_approx_of_totallyBounded htot δ hδ
    refine ⟨f '' t, htfin.image f, ?_⟩
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyt, hxy⟩
    apply Set.mem_iUnion.mpr ⟨f y, ?_⟩
    apply Set.mem_iUnion.mpr ⟨⟨y, hyt, rfl⟩, ?_⟩
    exact hcontrol x hx y (htE hyt) hxy
  exact himage.isBounded
