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
  let S : Set (closure E) := {x | (x : ℝ) ∈ E}
  have hS : Dense S := by
    rw [Subtype.dense_iff]
    have himage : ((↑) '' S : Set ℝ) = E := by
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, subset_closure hx⟩, hx, rfl⟩
    rw [himage]
  let F : S → ℝ := fun x => f x.1.1
  have hF : UniformContinuous F := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hf) ε hε
    refine ⟨δ, hδ, fun a b hab => ?_⟩
    exact hmod (a : ℝ) a.property (b : ℝ) b.property hab
  let g : ℝ → ℝ := fun x =>
    if hx : x ∈ closure E then hS.extend F ⟨x, hx⟩ else 0
  have hg_eq : ∀ x ∈ E, g x = f x := by
    intro x hx
    have hxc : x ∈ closure E := subset_closure hx
    let z : S := ⟨⟨x, hxc⟩, hx⟩
    have hz := hS.extend_of_ind hF z
    simpa [g, hxc, F, z] using hz
  have hg : UniformContinuousOn g (closure E) := by
    rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ :=
      (Metric.uniformContinuous_iff.mp (hS.uniformContinuous_extend hF)) ε hε
    refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
    have hxy' : dist (⟨x, hx⟩ : closure E) ⟨y, hy⟩ < δ := hxy
    simpa [g, hx, hy] using hmod hxy'
  have hcompact : IsCompact (closure E) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hE.closure
  obtain ⟨C, hC⟩ := dummy_assumed hcompact g hg
  refine (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨C, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  have hbound := hC x (subset_closure hx)
  rw [hg_eq x hx] at hbound
  simpa [Metric.mem_closedBall, Real.dist_eq] using hbound
