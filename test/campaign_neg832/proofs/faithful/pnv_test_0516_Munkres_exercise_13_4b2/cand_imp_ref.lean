import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (X : Type u) (α : Type v) (Tα : α → TopologicalSpace X) : ∃! (T : TopologicalSpace X), ∀ (a : α), Tα a ≤ T := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let toTop : (S : Set (Set X)) → is_topology X S → TopologicalSpace X :=
    fun S hS =>
      { IsOpen := fun s => s ∈ S
        isOpen_univ := hS.1
        isOpen_inter := hS.2.1
        isOpen_sUnion := hS.2.2 }
  let Tα : I → TopologicalSpace X := fun i => toTop (T i) (h i)
  obtain ⟨T', hT', hT'_unique⟩ := dummy_assumed X I Tα
  let S' : Set (Set X) := {s | T'.IsOpen s}
  have hS'_top : is_topology X S' := by
    exact ⟨@TopologicalSpace.isOpen_univ X T',
      @TopologicalSpace.isOpen_inter X T',
      @TopologicalSpace.isOpen_sUnion X T'⟩
  have hS'_sub : ∀ i, S' ⊆ T i := by
    intro i s hs
    exact (TopologicalSpace.le_def.mp (hT' i)) s hs
  have hS'_greatest : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ S' := by
    intro T'' hT'' hT''sub
    let U : TopologicalSpace X := toTop T'' hT''
    have hU : ∀ i, Tα i ≤ U := by
      intro i
      apply TopologicalSpace.le_def.mpr
      intro s hs
      exact hT''sub i hs
    have hUT' : U = T' := hT'_unique U hU
    intro s hs
    have hsU : U.IsOpen s := hs
    rw [hUT'] at hsU
    exact hsU
  refine ⟨S', ⟨hS'_top, hS'_sub, hS'_greatest⟩, ?_⟩
  intro S hS
  apply Set.Subset.antisymm
  · exact hS'_greatest S hS.1 hS.2.1
  · exact hS.2.2 S' hS'_top hS'_sub
