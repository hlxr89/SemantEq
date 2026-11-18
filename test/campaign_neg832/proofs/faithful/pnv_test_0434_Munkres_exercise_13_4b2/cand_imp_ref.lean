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
  rcases dummy_assumed X with ⟨τ, hτ⟩
  let T' : Set (Set X) := {s | τ.IsOpen s ∧ ∀ i, s ∈ T i}
  have hT' : is_topology X T' := by
    refine ⟨⟨τ.isOpen_univ, fun i => (h i).1⟩, ?_, ?_⟩
    · intro s t hs ht
      exact ⟨τ.isOpen_inter s t hs.1 ht.1, fun i => (h i).2.1 s t (hs.2 i) (ht.2 i)⟩
    · intro S hS
      exact ⟨τ.isOpen_sUnion S (fun s hs => (hS s hs).1),
        fun i => (h i).2.2 S (fun s hs => (hS s hs).2 i)⟩
  have hsub : ∀ i, T' ⊆ T i := fun i s hs => hs.2 i
  have hmax : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' htop hTi s hs
    let U : TopologicalSpace X :=
      { IsOpen := fun V => V ∈ T''
        isOpen_univ := htop.1
        isOpen_inter := htop.2.1
        isOpen_sUnion := htop.2.2 }
    exact ⟨hτ U s hs, fun i => hTi i hs⟩
  refine ⟨T', ⟨hT', hsub, hmax⟩, ?_⟩
  intro S hS
  apply Set.Subset.antisymm
  · exact hmax S hS.1 hS.2.1
  · exact hS.2.2 T' hT' hsub
