import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem exercise_13_4b2_assumed (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! t : TopologicalSpace X, (∀ i, t ≤ T i) ∧ (∀ t', (∀ i, t' ≤ T i) → t' ≤ t) := by
  let B := {u : TopologicalSpace X // ∀ i, u ≤ T i}
  let O : B → Set (Set X) := fun u => {s | IsOpen[(u : TopologicalSpace X)] s}
  have hO : ∀ u, is_topology X (O u) := by
    intro u
    refine ⟨@isOpen_univ X u, ?_, ?_⟩
    · intro s t hs ht
      exact @IsOpen.inter X u s t hs ht
    · intro S hS
      exact @isOpen_sUnion X u S hS
  obtain ⟨S, hS, hS_unique⟩ := exercise_13_4b2_assumed X B O hO
  let C : Set (Set X) := {s | ∀ u : B, s ∈ O u}
  have hC : is_topology X C := by
    refine ⟨fun u => @isOpen_univ X u, ?_, ?_⟩
    · intro s t hs ht u
      exact @IsOpen.inter X u s t (hs u) (ht u)
    · intro A hA u
      exact @isOpen_sUnion X u A (fun s hs => hA s hs u)
  have hCS : C ⊆ S := hS.2.2 C hC (fun u s hs => hs u)
  let t : TopologicalSpace X :=
    { IsOpen := fun s => s ∈ S
      isOpen_univ := hS.1.1
      isOpen_inter := fun s t hs ht => hS.1.2.1 s t hs ht
      isOpen_sUnion := fun A hA => hS.1.2.2 A hA }
  have ht_lower : ∀ i, t ≤ T i := by
    intro i s hs
    change s ∈ S
    apply hCS
    intro u
    exact u.property i s hs
  have ht_greatest : ∀ t', (∀ i, t' ≤ T i) → t' ≤ t := by
    intro t' ht' s hs
    change s ∈ S at hs
    let u : B := ⟨t', ht'⟩
    exact hS.2.1 u hs
  refine ⟨t, ⟨ht_lower, ht_greatest⟩, ?_⟩
  intro t' ht'
  apply TopologicalSpace.ext
  apply Set.ext
  intro s
  change IsOpen[t'] s ↔ IsOpen[t] s
  exact ⟨ht'.2 t ht_lower s, ht_greatest t' ht'.1 s⟩
