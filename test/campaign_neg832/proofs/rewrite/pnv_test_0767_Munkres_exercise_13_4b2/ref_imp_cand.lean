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
theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! S : TopologicalSpace X, (∀ i, S ≤ T i) ∧ ∀ T' : TopologicalSpace X, (∀ i, T' ≤ T i) → T' ≤ S := by
  let B := { U : TopologicalSpace X // ∀ i s, (T i).IsOpen s → U.IsOpen s }
  obtain ⟨O, hO, hO_unique⟩ :=
    exercise_13_4b2_assumed X B (fun U => U.1.IsOpen)
      (fun U => ⟨U.1.isOpen_univ, U.1.isOpen_inter, U.1.isOpen_sUnion⟩)
  let S : TopologicalSpace X :=
    { IsOpen := O
      isOpen_univ := hO.1.1
      isOpen_inter := hO.1.2.1
      isOpen_sUnion := hO.1.2.2 }
  have hS : (∀ i, S ≤ T i) ∧
      ∀ T' : TopologicalSpace X, (∀ i, T' ≤ T i) → T' ≤ S := by
    constructor
    · intro i
      exact hO.2.2 (T i).IsOpen
        ⟨(T i).isOpen_univ, (T i).isOpen_inter, (T i).isOpen_sUnion⟩
        (fun U => U.2 i)
    · intro T' hT'
      exact hO.2.1 ⟨T', hT'⟩
  refine ⟨S, hS, ?_⟩
  intro S' hS'
  apply le_antisymm
  · exact hS.2 S' hS'.1
  · exact hS'.2 S hS.1
