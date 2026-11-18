import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} (T : ι → TopologicalSpace X) : ∃ (t : TopologicalSpace X), ∀ (i : ι), t ≤ T i ∧ ∀ (t' : TopologicalSpace X), (∀ (i : ι), t' ≤ T i) → t' ≤ t := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let τ : I → TopologicalSpace X := fun i =>
    ⟨fun s => s ∈ T i, (h i).1, (h i).2.1, (h i).2.2⟩
  let J := {q : TopologicalSpace X //
    ∀ i, {s | @IsOpen X q s} ⊆ T i}
  let σ : Option J → TopologicalSpace X
    | none => ⊤
    | some q => q.1
  obtain ⟨t, ht⟩ := dummy_assumed σ
  let U : Set (Set X) := {s | @IsOpen X t s}
  have hU : is_topology X U ∧ (∀ i, U ⊆ T i) ∧
      ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ U := by
    refine ⟨⟨t.isOpen_univ, t.isOpen_inter, t.isOpen_sUnion⟩, ?_, ?_⟩
    · intro i s hs
      have hbounds : ∀ j, τ i ≤ σ j := by
        intro j
        cases j with
        | none => exact le_top
        | some q =>
            rw [TopologicalSpace.le_def]
            intro r hr
            change r ∈ T i
            exact q.2 i hr
      have hle : τ i ≤ t := (ht none).2 (τ i) hbounds
      change @IsOpen X t s at hs
      simpa [τ] using (TopologicalSpace.le_def.mp hle s hs)
    · intro T'' hT'' hsub s hs
      let t'' : TopologicalSpace X :=
        ⟨fun r => r ∈ T'', hT''.1, hT''.2.1, hT''.2.2⟩
      let q : J := ⟨t'', fun i r hr => hsub i hr⟩
      have hle : t ≤ t'' := by
        simpa [σ, q] using (ht (some q)).1
      change @IsOpen X t'' s at hs
      change @IsOpen X t s
      exact (TopologicalSpace.le_def.mp hle) s hs
  refine ⟨U, hU, ?_⟩
  intro V hV
  apply Set.Subset.antisymm
  · exact hU.2.2 V hV.1 hV.2.1
  · exact hV.2.2 U hU.1 hU.2.1
