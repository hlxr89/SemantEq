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
  rcases dummy_assumed X with ⟨B, hB⟩
  let T' : Set (Set X) := {s | (∀ i, s ∈ T i) ∧ B.IsOpen s}
  have hT' : is_topology X T' := by
    refine ⟨⟨fun i => (h i).1, B.isOpen_univ⟩, ?_, ?_⟩
    · intro s t hs ht
      exact ⟨fun i => (h i).2.1 s t (hs.1 i) (ht.1 i), B.isOpen_inter s t hs.2 ht.2⟩
    · intro S hS
      exact ⟨fun i => (h i).2.2 S (fun s hs => (hS s hs).1 i),
        B.isOpen_sUnion S (fun s hs => (hS s hs).2)⟩
  have hgreat : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' hT'' hsub s hs
    let U : TopologicalSpace X :=
      { IsOpen := fun V => V ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    exact ⟨fun i => hsub i hs, (hB U) s hs⟩
  refine ⟨T', ⟨hT', fun i s hs => hs.1 i, hgreat⟩, ?_⟩
  intro T'' hT''
  apply Set.Subset.antisymm
  · exact hgreat T'' hT''.1 hT''.2.1
  · exact hT''.2.2 T' hT' (fun i s hs => hs.1 i)
