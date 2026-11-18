import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed [TopologicalSpace X] {α : Type*} (Ta : α → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ (a : α), τ ≤ Ta a) ∧ ∀ τ' : TopologicalSpace X, (∀ (a : α), τ' ≤ Ta a) → τ ≤ τ' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let T' : Set (Set X) := {s | ∀ i, s ∈ T i}
  refine ⟨T', ?_, ?_⟩
  · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact fun i => (h i).1
    · intro s t hs ht i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro S hS i
      exact (h i).2.2 S fun t ht => hS t ht i
    · exact fun i s hs => hs i
    · intro T'' _ hT'' s hs i
      exact hT'' i hs
  · intro T'' hT''
    apply Set.Subset.antisymm
    · exact fun s hs i => hT''.2.1 i hs
    · exact hT''.2.2 T' (by
        refine ⟨?_, ?_, ?_⟩
        · exact fun i => (h i).1
        · intro s t hs ht i
          exact (h i).2.1 s t (hs i) (ht i)
        · intro S hS i
          exact (h i).2.2 S fun t ht => hS t ht i) (fun i s hs => hs i)
