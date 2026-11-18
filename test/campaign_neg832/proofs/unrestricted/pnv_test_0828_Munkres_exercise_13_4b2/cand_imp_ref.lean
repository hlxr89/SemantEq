import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (X : Type u) (T : ι → TopologicalSpace X) : ∃ (m : TopologicalSpace X), (∀ i, T i ≤ m) ∧ ∀ (t : TopologicalSpace X) (h : ∀ i, T i ≤ t), m ≤ t := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let t : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  obtain ⟨m, hm_upper, hm_least⟩ := dummy_assumed X t
  let T' : Set (Set X) := {s | IsOpen[ m ] s}
  have hT' : is_topology X T' :=
    ⟨isOpen_univ, fun _ _ => IsOpen.inter, fun _ => isOpen_sUnion⟩
  have hsub : ∀ i, T' ⊆ T i := hm_upper
  have hmax : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' hT'' hTsub
    let t'' : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    exact hm_least t'' hTsub
  refine ⟨T', ⟨hT', hsub, hmax⟩, ?_⟩
  intro S hS
  apply Set.Subset.antisymm
  · exact hmax S hS.1 hS.2.1
  · exact hS.2.2 T' hT' hsub
