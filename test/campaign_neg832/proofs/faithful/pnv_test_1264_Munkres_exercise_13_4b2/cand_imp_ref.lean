import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! t : TopologicalSpace X, (∀ i, t ≤ T i) ∧ (∀ t', (∀ i, t' ≤ T i) → t' ≤ t) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let τ : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := fun s t hs ht => (h i).2.1 s t hs ht
      isOpen_sUnion := fun A hA => (h i).2.2 A hA }
  let B := {u : TopologicalSpace X // ∀ i, τ i ≤ u}
  let F : B → TopologicalSpace X := fun u => u
  obtain ⟨t, ht, ht_unique⟩ := dummy_assumed F
  let S : Set (Set X) := {s | IsOpen[t] s}
  have hS_top : is_topology X S := by
    refine ⟨@isOpen_univ X t, ?_, ?_⟩
    · intro s u hs hu
      exact IsOpen.inter hs hu
    · intro A hA
      exact isOpen_sUnion hA
  have hS_sub : ∀ i, S ⊆ T i := by
    intro i s hs
    have hi : ∀ u : B, τ i ≤ F u := fun u => u.property i
    have hit : τ i ≤ t := ht.2 (τ i) hi
    exact hit s hs
  have hS_max : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ S := by
    intro T'' hT'' hT''sub
    let u : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := fun s v hs hv => hT''.2.1 s v hs hv
        isOpen_sUnion := fun A hA => hT''.2.2 A hA }
    have hu : ∀ i, τ i ≤ u := by
      intro i s hs
      exact hT''sub i hs
    let b : B := ⟨u, hu⟩
    have htu : t ≤ u := ht.1 b
    intro s hs
    exact htu s hs
  refine ⟨S, ⟨hS_top, hS_sub, hS_max⟩, ?_⟩
  intro S' hS'
  apply Set.Subset.antisymm
  · exact hS_max S' hS'.1 hS'.2.1
  · exact hS'.2.2 S hS_top hS_sub
