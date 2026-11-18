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
  letI : TopologicalSpace X := ⊥
  let Ta : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := fun s t hs ht => (h i).2.1 s t hs ht
      isOpen_sUnion := fun s hs => (h i).2.2 s hs }
  obtain ⟨τ, hτ, hτ_unique⟩ := dummy_assumed Ta
  let T' : Set (Set X) := {s | ∀ i, s ∈ T i}
  have hT' : is_topology X T' := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      exact (h i).1
    · intro s t hs ht i
      exact (h i).2.1 s t (hs i) (ht i)
    · intro s hs i
      exact (h i).2.2 s (fun t ht => hs t ht i)
  have hT'_sub : ∀ i, T' ⊆ T i := by
    intro i s hs
    exact hs i
  refine ⟨T', ⟨hT', hT'_sub, ?_⟩, ?_⟩
  · intro T'' hT'' hT''_sub s hs i
    exact hT''_sub i hs
  · intro U hU
    apply Set.ext
    intro s
    constructor
    · intro hs i
      exact hU.2.1 i hs
    · intro hs
      exact hU.2.2 T' hT' hT'_sub hs
