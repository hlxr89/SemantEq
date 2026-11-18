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
  let τi : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := fun s t hs ht => (h i).2.1 s t hs ht
      isOpen_sUnion := fun s hs => (h i).2.2 s hs }
  let J := {τ' : TopologicalSpace X // ∀ i : I, τi i ≤ τ'}
  obtain ⟨τ, hτ, -⟩ := dummy_assumed (fun j : J => j.1)
  let T' : Set (Set X) := {s | IsOpen[τ] s}
  have hT'_top : is_topology X T' := by
    exact ⟨isOpen_univ, fun s t hs ht => hs.inter ht,
      fun s hs => isOpen_sUnion hs⟩
  have hT'_lower : ∀ i, T' ⊆ T i := by
    intro i s hs
    change IsOpen[τ] s at hs
    have hi : τi i ≤ τ := hτ.2 (τi i) (by
      intro j
      exact j.2 i)
    exact hi s hs
  have hT'_greatest : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
    intro T'' hT'' hT''_lower s hs
    let τ'' : TopologicalSpace X :=
      { IsOpen := fun u => u ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := fun u v hu hv => hT''.2.1 u v hu hv
        isOpen_sUnion := fun U hU => hT''.2.2 U hU }
    have hτ''_upper : ∀ i : I, τi i ≤ τ'' := by
      intro i u hu
      exact hT''_lower i hu
    have hτ_le : τ ≤ τ'' := hτ.1 ⟨τ'', hτ''_upper⟩
    change IsOpen[τ] s
    exact hτ_le s hs
  refine ⟨T', ⟨hT'_top, hT'_lower, hT'_greatest⟩, ?_⟩
  intro T'' hT''
  apply Set.Subset.antisymm
  · exact hT'_greatest T'' hT''.1 hT''.2.1
  · exact hT''.2.2 T' hT'_top hT'_lower
