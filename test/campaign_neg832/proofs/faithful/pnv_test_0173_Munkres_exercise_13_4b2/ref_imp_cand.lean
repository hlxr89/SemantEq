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
theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! T₀ : TopologicalSpace X, (∀ α, T₀ ≤ T α) ∧ (∀ T', (∀ α, T' ≤ T α) → T' ≤ T₀) := by
  let L := {t : TopologicalSpace X // ∀ α, t ≤ T α}
  let O : L → Set (Set X) := fun t => {s | IsOpen[t.1] s}
  have hO : ∀ t, is_topology X (O t) := by
    intro t
    exact ⟨t.1.isOpen_univ, t.1.isOpen_inter, t.1.isOpen_sUnion⟩
  obtain ⟨S, hS, _⟩ := exercise_13_4b2_assumed X L O hO
  let T₀ : TopologicalSpace X :=
    { IsOpen := fun s => s ∈ S
      isOpen_univ := hS.1.1
      isOpen_inter := hS.1.2.1
      isOpen_sUnion := hS.1.2.2 }
  have hT₀ : (∀ α, T₀ ≤ T α) ∧ (∀ T', (∀ α, T' ≤ T α) → T' ≤ T₀) := by
    constructor
    · intro α
      apply hS.2.2 {s | IsOpen[T α] s}
        ⟨(T α).isOpen_univ, (T α).isOpen_inter, (T α).isOpen_sUnion⟩
      intro t U hU
      exact t.2 α U hU
    · intro T' hT'
      exact hS.2.1 ⟨T', hT'⟩
  refine ⟨T₀, hT₀, ?_⟩
  intro T₁ hT₁
  exact le_antisymm (hT₀.2 T₁ hT₁.1) (hT₁.2 T₀ hT₀.1)
