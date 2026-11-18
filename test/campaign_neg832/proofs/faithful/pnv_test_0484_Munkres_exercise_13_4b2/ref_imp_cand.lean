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
theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ i, τ ≤ T i) ∧ ∀ τ', (∀ i, τ' ≤ T i) → τ' ≤ τ := by
  let J := {τ : TopologicalSpace X // ∀ i, τ ≤ T i}
  let O : J → Set (Set X) := fun j => {s | j.1.IsOpen s}
  have hO : ∀ j, is_topology X (O j) := by
    intro j
    exact ⟨j.1.isOpen_univ, fun s t hs ht => j.1.isOpen_inter s t hs ht,
      fun s hs => j.1.isOpen_sUnion s hs⟩
  obtain ⟨U, hU, _⟩ := exercise_13_4b2_assumed X J O hO
  let τ : TopologicalSpace X :=
    { IsOpen := fun s => s ∈ U
      isOpen_univ := hU.1.1
      isOpen_inter := hU.1.2.1
      isOpen_sUnion := hU.1.2.2 }
  have hτ : ∀ i, τ ≤ T i := by
    intro i
    change ∀ s, (T i).IsOpen s → τ.IsOpen s
    intro s hs
    change s ∈ U
    apply hU.2.2 (T i).IsOpen
    · exact ⟨(T i).isOpen_univ, fun a b ha hb => (T i).isOpen_inter a b ha hb,
        fun a ha => (T i).isOpen_sUnion a ha⟩
    · intro j a ha
      have hj := j.2 i
      change ∀ s, (T i).IsOpen s → j.1.IsOpen s at hj
      simpa [O] using hj a ha
    · exact hs
  have hmax : ∀ τ', (∀ i, τ' ≤ T i) → τ' ≤ τ := by
    intro τ' hτ'
    change ∀ s, τ.IsOpen s → τ'.IsOpen s
    intro s hs
    change s ∈ U at hs
    exact hU.2.1 ⟨τ', hτ'⟩ hs
  refine ⟨τ, ⟨hτ, hmax⟩, ?_⟩
  intro τ' hτ'prop
  exact le_antisymm (hmax τ' hτ'prop.1) (hτ'prop.2 τ hτ)
