import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (X : Type u) : ∃ (T : TopologicalSpace X), ∀ (U : TopologicalSpace X), T ≤ U := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  have htop : is_topology X (⋂ i, T i) := by
    constructor
    · simp only [mem_iInter]
      intro i
      exact (h i).1
    constructor
    · intro s t hs ht
      simp only [mem_iInter] at hs ht ⊢
      intro i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro S hS
      simp only [mem_iInter] at hS ⊢
      intro i
      exact (h i).2.2 S (fun t ht => hS t ht i)
  have hsub : ∀ i, (⋂ i, T i) ⊆ T i := by
    intro i s hs
    exact mem_iInter.mp hs i
  refine ⟨⋂ i, T i, ⟨htop, hsub, ?_⟩, ?_⟩
  · intro T'' _ hT'' s hs
    exact mem_iInter.mpr (fun i => hT'' i hs)
  · intro T' hT'
    apply Set.Subset.antisymm
    · intro s hs
      exact mem_iInter.mpr (fun i => hT'.2.1 i hs)
    · exact hT'.2.2 (⋂ i, T i) htop hsub
