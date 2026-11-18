import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! τ : TopologicalSpace X, (∀ i, τ ≤ T i) ∧ ∀ τ', (∀ i, τ' ≤ T i) → τ' ≤ τ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let τi : I → TopologicalSpace X := fun i =>
    ⟨fun s => s ∈ T i, (h i).1, (h i).2.1, (h i).2.2⟩
  let B := {σ : TopologicalSpace X // ∀ i, {s | IsOpen[σ] s} ⊆ T i}
  obtain ⟨τ, hτ, hτ_unique⟩ := dummy_assumed (fun σ : B => σ.1)
  let U : Set (Set X) := {s | IsOpen[τ] s}
  refine ⟨U, ?_, ?_⟩
  · constructor
    · exact ⟨isOpen_univ, fun _ _ => IsOpen.inter, fun _ => isOpen_sUnion⟩
    constructor
    · intro i s hs
      exact hτ.2 (τi i) (fun σ u hu => σ.2 i hu) s hs
    · intro V hV hVi s hs
      let σ : TopologicalSpace X :=
        ⟨fun u => u ∈ V, hV.1, hV.2.1, hV.2.2⟩
      exact hτ.1 ⟨σ, hVi⟩ s hs
  · intro V hV
    let σ : TopologicalSpace X :=
      ⟨fun u => u ∈ V, hV.1.1, hV.1.2.1, hV.1.2.2⟩
    have hσ : (∀ b : B, σ ≤ b.1) ∧ ∀ σ', (∀ b : B, σ' ≤ b.1) → σ' ≤ σ := by
      constructor
      · intro b s hs
        exact hV.2.2 {u | IsOpen[b.1] u}
          ⟨b.1.isOpen_univ, b.1.isOpen_inter, b.1.isOpen_sUnion⟩ b.2 hs
      · intro σ' hσ' s hs
        exact hσ' ⟨σ, hV.2.1⟩ s hs
    have heq : σ = τ := hτ_unique σ hσ
    apply Set.ext
    intro s
    change IsOpen[σ] s ↔ IsOpen[τ] s
    rw [heq]
