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
  let J := {τ' : TopologicalSpace X // ∀ i : I, τ' ≤ T i}
  let O : J → Set (Set X) := fun j => {s | IsOpen[j.1] s}
  have hO : ∀ j, is_topology X (O j) := by
    intro j
    exact ⟨j.1.isOpen_univ, fun s t hs ht => j.1.isOpen_inter s t hs ht,
      fun s hs => j.1.isOpen_sUnion s hs⟩
  obtain ⟨O', hO', -⟩ := exercise_13_4b2_assumed X J O hO
  let Ocap : Set (Set X) := {s | ∀ j : J, s ∈ O j}
  have hOcap_top : is_topology X Ocap := by
    exact ⟨fun j => (hO j).1,
      fun s t hs ht j => (hO j).2.1 s t (hs j) (ht j),
      fun s hs j => (hO j).2.2 s (fun u hu => hs u hu j)⟩
  have hOcap_lower : ∀ j, Ocap ⊆ O j := by
    intro j s hs
    exact hs j
  have hOcap_to_O' : Ocap ⊆ O' :=
    hO'.2.2 Ocap hOcap_top hOcap_lower
  let τ : TopologicalSpace X :=
    { IsOpen := fun s => s ∈ O'
      isOpen_univ := hO'.1.1
      isOpen_inter := fun s t hs ht => hO'.1.2.1 s t hs ht
      isOpen_sUnion := fun s hs => hO'.1.2.2 s hs }
  have hτ_lower : ∀ i : I, τ ≤ T i := by
    intro i s hs
    change s ∈ O'
    apply hOcap_to_O'
    intro j
    exact j.2 i s hs
  have hτ_greatest : ∀ τ' : TopologicalSpace X, (∀ i : I, τ' ≤ T i) → τ' ≤ τ := by
    intro τ' hτ' s hs
    change s ∈ O' at hs
    exact hO'.2.1 ⟨τ', hτ'⟩ hs
  refine ⟨τ, ⟨hτ_lower, hτ_greatest⟩, ?_⟩
  intro τ' hτ'
  exact le_antisymm (hτ_greatest τ' hτ'.1) (hτ'.2 τ hτ_lower)
