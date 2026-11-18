import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem exercise_13_4b2_assumed (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy [TopologicalSpace X] {α : Type*} (Ta : α → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ (a : α), τ ≤ Ta a) ∧ ∀ τ' : TopologicalSpace X, (∀ (a : α), τ' ≤ Ta a) → τ ≤ τ' := by
  have h_all : is_topology X (Set.univ : Set (Set X)) := by
    refine ⟨Set.mem_univ univ, ?_, ?_⟩
    · intro s t hs ht
      exact Set.mem_univ (s ∩ t)
    · intro s hs
      exact Set.mem_univ (sUnion s)
  obtain ⟨T', hT', hT'_unique⟩ :=
    exercise_13_4b2_assumed X (Set X) (fun _ => Set.univ) (fun _ => h_all)
  have h_every : ∀ s : Set X, s ∈ T' := by
    intro s
    exact hT'.2.2 Set.univ h_all (fun _ => Set.Subset.rfl) (Set.mem_univ s)
  let τ : TopologicalSpace X :=
    { IsOpen := fun s => s ∈ T'
      isOpen_univ := hT'.1.1
      isOpen_inter := hT'.1.2.1
      isOpen_sUnion := hT'.1.2.2 }
  have hτ : (∀ (a : α), τ ≤ Ta a) ∧
      ∀ τ' : TopologicalSpace X, (∀ (a : α), τ' ≤ Ta a) → τ ≤ τ' := by
    constructor
    · intro a s hs
      exact h_every s
    · intro τ' hτ' s hs
      exact h_every s
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  apply le_antisymm
  · exact hτ'.2 τ hτ.1
  · exact hτ.2 τ' hτ'.1
