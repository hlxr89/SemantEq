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
  let T' : Set (Set X) := {s | ∀ i, s ∈ T i}
  have htop : is_topology X T' := by
    refine ⟨fun i ↦ (h i).1, ?_, ?_⟩
    · intro s t hs ht i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro s hs i
      exact (h i).2.2 s (fun t ht ↦ hs t ht i)
  have hlower : ∀ i, T' ⊆ T i := fun i s hs ↦ hs i
  refine ⟨T', ⟨htop, hlower, ?_⟩, ?_⟩
  · intro T'' _ hsub s hs i
    exact hsub i hs
  · intro T'' hT''
    apply Set.Subset.antisymm
    · exact fun s hs i ↦ hT''.2.1 i hs
    · exact hT''.2.2 T' htop hlower
