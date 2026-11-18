import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! S : TopologicalSpace X, (∀ i, S ≤ T i) ∧ ∀ T' : TopologicalSpace X, (∀ i, T' ≤ T i) → T' ≤ S := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let U : Set (Set X) := {s | ∀ i, s ∈ T i}
  have hU : is_topology X U := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (h i).1
    · intro s t hs ht i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro s hs i
      exact (h i).2.2 s fun t ht => hs t ht i
  have hsub : ∀ i, U ⊆ T i := fun i s hs => hs i
  refine ⟨U, ⟨hU, hsub, ?_⟩, ?_⟩
  · intro T'' _ hT'' s hs i
    exact hT'' i hs
  · rintro T'' ⟨hT'', hsub', hmax⟩
    apply Set.Subset.antisymm
    · intro s hs i
      exact hsub' i hs
    · exact hmax U hU hsub
