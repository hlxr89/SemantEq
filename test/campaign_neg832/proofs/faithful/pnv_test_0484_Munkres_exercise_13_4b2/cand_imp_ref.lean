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
  let τ : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  let J := {σ : TopologicalSpace X // ∀ i, τ i ≤ σ}
  obtain ⟨σ, hσ, _⟩ := dummy_assumed (fun j : J => j.1)
  let U : Set (Set X) := {s | σ.IsOpen s}
  have hupper : ∀ i, τ i ≤ σ := by
    intro i
    apply hσ.2 (τ i)
    intro j
    exact j.2 i
  have hUsub : ∀ i, U ⊆ T i := by
    intro i s hs
    exact (TopologicalSpace.le_def.mp (hupper i)) s hs
  have hUtop : is_topology X U :=
    ⟨σ.isOpen_univ, fun a b ha hb => σ.isOpen_inter a b ha hb,
      fun a ha => σ.isOpen_sUnion a ha⟩
  have hgreatest : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ U := by
    intro T'' hT'' hsub
    let σ' : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    have hσ' : σ ≤ σ' := hσ.1 ⟨σ', by
      intro i
      rw [TopologicalSpace.le_def]
      exact hsub i⟩
    intro s hs
    exact (TopologicalSpace.le_def.mp hσ') s hs
  refine ⟨U, ⟨hUtop, hUsub, hgreatest⟩, ?_⟩
  intro U' hU'
  apply Set.Subset.antisymm
  · exact hgreatest U' hU'.1 hU'.2.1
  · exact hU'.2.2 U hUtop hUsub
