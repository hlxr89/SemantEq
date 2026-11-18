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
  let B := {σ : TopologicalSpace X // ∀ i, σ ≤ T i}
  let O : B → Set (Set X) := fun σ => {s | IsOpen[σ.1] s}
  have hO : ∀ σ, is_topology X (O σ) := fun σ =>
    ⟨σ.1.isOpen_univ, σ.1.isOpen_inter, σ.1.isOpen_sUnion⟩
  obtain ⟨U, hU, hU_unique⟩ := exercise_13_4b2_assumed X B O hO
  let τ : TopologicalSpace X :=
    ⟨fun s => s ∈ U, hU.1.1, hU.1.2.1, hU.1.2.2⟩
  refine ⟨τ, ?_, ?_⟩
  · constructor
    · intro i s hs
      change s ∈ U
      exact hU.2.2 {u | IsOpen[T i] u}
        ⟨(T i).isOpen_univ, (T i).isOpen_inter, (T i).isOpen_sUnion⟩
        (fun σ u hu => σ.2 i u hu) hs
    · intro τ' hτ' s hs
      change s ∈ U at hs
      exact hU.2.1 ⟨τ', hτ'⟩ hs
  · intro τ' hτ'
    apply TopologicalSpace.ext
    have hsets : {s | IsOpen[τ'] s} = U := hU_unique {s | IsOpen[τ'] s} (by
      constructor
      · exact ⟨τ'.isOpen_univ, τ'.isOpen_inter, τ'.isOpen_sUnion⟩
      constructor
      · intro σ s hs
        exact hτ'.2 σ.1 σ.2 s hs
      · intro V hV hVi s hs
        exact hVi ⟨τ', hτ'.1⟩ hs)
    exact hsets
