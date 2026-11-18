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
    { IsOpen := T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  let J := {τ : TopologicalSpace X // ∀ i, τi i ≤ τ}
  obtain ⟨τ, hτ, _⟩ := dummy_assumed (fun j : J => j.1)
  rcases hτ with ⟨hτlower, hτgreatest⟩
  have hiτ : ∀ i, τi i ≤ τ := by
    intro i
    apply hτgreatest
    intro j
    exact j.2 i
  let V : Set (Set X) := {s | IsOpen[τ] s}
  have hVtop : is_topology X V :=
    ⟨τ.isOpen_univ, fun s t hs ht => τ.isOpen_inter s t hs ht,
      fun s hs => τ.isOpen_sUnion s hs⟩
  have hVsub : ∀ i, V ⊆ T i := by
    intro i
    exact TopologicalSpace.le_def.mp (hiτ i)
  have hVmax : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ V := by
    intro T'' hT'' hT''sub
    let τ'' : TopologicalSpace X :=
      { IsOpen := T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    have hτiτ'' : ∀ i, τi i ≤ τ'' := by
      intro i
      rw [TopologicalSpace.le_def]
      exact hT''sub i
    have hττ'' : τ ≤ τ'' := hτlower ⟨τ'', hτiτ''⟩
    exact TopologicalSpace.le_def.mp hττ''
  refine ⟨V, ⟨hVtop, hVsub, hVmax⟩, ?_⟩
  intro V' hV'
  apply Set.Subset.antisymm
  · exact hVmax V' hV'.1 hV'.2.1
  · exact hV'.2.2 V hVtop hVsub
