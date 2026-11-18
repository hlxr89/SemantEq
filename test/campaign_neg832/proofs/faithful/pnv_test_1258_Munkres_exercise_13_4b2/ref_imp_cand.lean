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
theorem dummy {X : Type*} {I : Type*} (T : I → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ i : I, τ ≤ T i) ∧ (∀ τ' : TopologicalSpace X, (∀ i : I, τ' ≤ T i) → τ' ≤ τ) := by
  let J := {τ : TopologicalSpace X // ∀ i, τ ≤ T i}
  let U : J → Set (Set X) := fun j => {s | IsOpen[j.1] s}
  have hU : ∀ j, is_topology X (U j) := by
    intro j
    exact ⟨j.1.isOpen_univ, fun s t hs ht => j.1.isOpen_inter s t hs ht,
      fun s hs => j.1.isOpen_sUnion s hs⟩
  obtain ⟨V, hV, _⟩ := exercise_13_4b2_assumed X J U hU
  rcases hV with ⟨hVtop, hVsub, hVmax⟩
  let τ : TopologicalSpace X :=
    { IsOpen := V
      isOpen_univ := hVtop.1
      isOpen_inter := hVtop.2.1
      isOpen_sUnion := hVtop.2.2 }
  have hTall : is_topology X {s | ∀ j : J, IsOpen[j.1] s} := by
    refine ⟨?_, ?_, ?_⟩
    · intro j
      exact j.1.isOpen_univ
    · intro s t hs ht j
      exact j.1.isOpen_inter s t (hs j) (ht j)
    · intro s hs j
      exact j.1.isOpen_sUnion s (fun t ht => hs t ht j)
  have hTallV : {s | ∀ j : J, IsOpen[j.1] s} ⊆ V := by
    apply hVmax _ hTall
    intro j s hs
    exact hs j
  have hτ_lower : ∀ i : I, τ ≤ T i := by
    intro i
    rw [TopologicalSpace.le_def]
    intro s hs
    apply hTallV
    intro j
    exact TopologicalSpace.le_def.mp (j.2 i) s hs
  have hτ_greatest : ∀ τ' : TopologicalSpace X, (∀ i : I, τ' ≤ T i) → τ' ≤ τ := by
    intro τ' hτ'
    rw [TopologicalSpace.le_def]
    intro s hs
    exact hVsub ⟨τ', hτ'⟩ hs
  refine ⟨τ, ⟨hτ_lower, hτ_greatest⟩, ?_⟩
  · intro τ' hτ'prop
    apply le_antisymm
    · exact hτ_greatest τ' hτ'prop.1
    · exact hτ'prop.2 τ hτ_lower
