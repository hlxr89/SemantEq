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
  let T' : Set (Set X) := {s | ∀ i, s ∈ T i}
  have htop : is_topology X T' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (h i).1
    · intro s t hs ht i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro S hS i
      exact (h i).2.2 S (by
        intro s hs
        exact hS s hs i)
  have hsub : ∀ i, T' ⊆ T i := by
    intro i s hs
    exact hs i
  have hgreatest : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' _ hT'' s hs i
    exact hT'' i hs
  refine ⟨T', ⟨htop, hsub, hgreatest⟩, ?_⟩
  intro U hU
  apply Set.Subset.antisymm
  · exact hgreatest U hU.1 hU.2.1
  · exact hU.2.2 T' htop hsub
