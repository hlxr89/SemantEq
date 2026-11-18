import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! t : TopologicalSpace X, (∀ α, t ≤ T α) ∧ (∀ t', (∀ α, t' ≤ T α) → t' ≤ t) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let T' : Set (Set X) := {s | ∀ i, s ∈ T i}
  have htop : is_topology X T' := by
    refine ⟨?_, ?_, ?_⟩
    · exact fun i => (h i).1
    · intro s t hs ht
      exact fun i => (h i).2.1 s t (hs i) (ht i)
    · intro S hS
      exact fun i => (h i).2.2 S (fun t ht => hS t ht i)
  have hsub : ∀ i, T' ⊆ T i := fun i s hs => hs i
  have hgreat : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' :=
    fun T'' _ hsub' s hs i => hsub' i hs
  refine ⟨T', ⟨htop, hsub, hgreat⟩, ?_⟩
  intro U hU
  apply Set.Subset.antisymm
  · exact hgreat U hU.1 hU.2.1
  · exact hU.2.2 T' htop hsub
