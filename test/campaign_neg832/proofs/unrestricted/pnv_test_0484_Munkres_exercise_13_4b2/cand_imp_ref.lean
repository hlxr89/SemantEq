import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ i, τ ≤ T i) ∧ ∀ τ', (∀ i, τ' ≤ T i) → τ' ≤ τ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let U : Set (Set X) := {s | ∀ i, s ∈ T i}
  have hU_top : is_topology X U := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (h i).1
    · intro s t hs ht i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro S hS i
      apply (h i).2.2 S
      intro t ht
      exact hS t ht i
  have hU_sub : ∀ i, U ⊆ T i := by
    intro i s hs
    exact hs i
  have hU_max : ∀ V, is_topology X V → (∀ i, V ⊆ T i) → V ⊆ U := by
    intro V _ hV s hs i
    exact hV i hs
  refine ⟨U, ⟨hU_top, hU_sub, hU_max⟩, ?_⟩
  intro V hV
  apply Set.Subset.antisymm
  · exact hU_max V hV.1 hV.2.1
  · exact hV.2.2 U hU_top hU_sub
