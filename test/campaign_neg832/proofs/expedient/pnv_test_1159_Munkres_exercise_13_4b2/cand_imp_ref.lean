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
  let T' : Set (Set X) := ⋂ i, T i
  have htop : is_topology X T' := by
    refine ⟨?_, ?_, ?_⟩
    · exact mem_iInter.mpr fun i => (h i).1
    · intro s t hs ht
      exact mem_iInter.mpr fun i => (h i).2.1 s t (mem_iInter.mp hs i) (mem_iInter.mp ht i)
    · intro s hs
      exact mem_iInter.mpr fun i => (h i).2.2 s fun t ht => mem_iInter.mp (hs t ht) i
  have hsub : ∀ i, T' ⊆ T i := fun i => iInter_subset T i
  have hgreat : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' _ hT''
    exact fun s hs => mem_iInter.mpr fun i => hT'' i hs
  refine ⟨T', ⟨htop, hsub, hgreat⟩, ?_⟩
  intro U hU
  apply Set.Subset.antisymm
  · exact hgreat U hU.1 hU.2.1
  · exact hU.2.2 T' htop hsub
