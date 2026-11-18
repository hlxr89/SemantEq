import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (Tα : ι → TopologicalSpace X) : ∃ (T : TopologicalSpace X), ∀ (α : ι), Tα α ≤ T := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let Tα : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  obtain ⟨Tb, hTb⟩ := dummy_assumed Tα
  let T' : Set (Set X) := {s | ∀ i, s ∈ T i}
  have hT' : is_topology X T' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact hTb i univ isOpen_univ
    · intro s t hs ht i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro S hS i
      exact (h i).2.2 S fun s hs => hS s hs i
  refine ⟨T', ⟨hT', ?_, ?_⟩, ?_⟩
  · intro i s hs
    exact hs i
  · intro T'' _ hsub s hs i
    exact hsub i hs
  · intro U hU
    apply Set.Subset.antisymm
    · intro s hs i
      exact hU.2.1 i hs
    · apply hU.2.2 T' hT'
      intro i s hs
      exact hs i
