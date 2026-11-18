import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} {I : Type*} (T : I → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ i : I, τ ≤ T i) ∧ (∀ τ' : TopologicalSpace X, (∀ i : I, τ' ≤ T i) → τ' ≤ τ) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let S : Set (Set X) := {U | ∀ i, U ∈ T i}
  have hS : is_topology X S := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (h i).1
    · intro s t hs ht i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro A hA i
      exact (h i).2.2 A (fun U hU => hA U hU i)
  have hSsub : ∀ i, S ⊆ T i := by
    intro i U hU
    exact hU i
  have hSgreatest : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ S := by
    intro T'' _ hsub U hU i
    exact hsub i hU
  refine ⟨S, ⟨hS, hSsub, hSgreatest⟩, ?_⟩
  intro S' hS'
  apply Set.Subset.antisymm
  · exact hSgreatest S' hS'.1 hS'.2.1
  · exact hS'.2.2 S hS hSsub
