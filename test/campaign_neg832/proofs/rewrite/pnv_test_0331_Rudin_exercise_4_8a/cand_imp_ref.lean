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
  classical
  let e : E → closure E := Set.inclusion subset_closure
  have he : IsUniformInducing e :=
    (isUniformEmbedding_set_inclusion subset_closure).isUniformInducing
  have hed : DenseRange e :=
    (denseRange_inclusion_iff subset_closure).2 subset_rfl
  have hfr : UniformContinuous (E.restrict f) :=
    uniformContinuousOn_iff_restrict.mp hf
  let F : closure E → ℝ := (he.isDenseInducing hed).extend (E.restrict f)
  have hF : UniformContinuous F :=
    uniformContinuous_uniformly_extend he hed hfr
  let g : ℝ → ℝ := fun x ↦ if hx : x ∈ closure E then F ⟨x, hx⟩ else 0
  have hg : UniformContinuousOn g (closure E) := by
    rw [uniformContinuousOn_iff_restrict]
    have hgf : (closure E).restrict g = F := by
      funext x
      simp only [Set.restrict_apply, g, dif_pos x.property]
    rw [hgf]
    exact hF
  obtain ⟨C, hC⟩ := dummy_assumed hE.isCompact_closure g hg
  refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hFx : F (e ⟨x, hx⟩) = f x :=
    uniformly_extend_of_ind he hed hfr ⟨x, hx⟩
  have hgx : g x = f x := by
    dsimp only [g]
    rw [dif_pos (subset_closure hx)]
    exact hFx
  simpa only [Real.norm_eq_abs, hgx] using hC x (subset_closure hx)
