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
  have hAll : ∀ _ : Unit, is_topology X (Set.univ : Set (Set X)) := by
    intro _
    simp [is_topology]
  obtain ⟨T', hT', _⟩ :=
    exercise_13_4b2_assumed X Unit (fun _ => (Set.univ : Set (Set X))) hAll
  have hTop : is_topology X T' := hT'.1
  have hEvery : ∀ s : Set X, s ∈ T' := by
    intro s
    exact hT'.2.2 Set.univ (by simp [is_topology]) (by simp) (by simp)
  let τ : TopologicalSpace X :=
    TopologicalSpace.mk (fun s => s ∈ T') hTop.1 hTop.2.1 hTop.2.2
  have hτ : (∀ (a : α), τ ≤ Ta a) ∧
      ∀ τ' : TopologicalSpace X, (∀ (a : α), τ' ≤ Ta a) → τ ≤ τ' := by
    constructor
    · intro a
      rw [TopologicalSpace.le_def]
      intro s _
      exact hEvery s
    · intro τ' _
      rw [TopologicalSpace.le_def]
      intro s _
      exact hEvery s
  refine ⟨τ, hτ, ?_⟩
  intro τ' hτ'
  exact le_antisymm (hτ'.2 τ hτ.1) (hτ.2 τ' hτ'.1)
