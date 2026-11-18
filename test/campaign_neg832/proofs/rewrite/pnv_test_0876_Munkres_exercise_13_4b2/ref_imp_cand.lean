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
theorem dummy {X : Type*} (T : ι → TopologicalSpace X) : ∃! t : TopologicalSpace X, (∀ α, t ≤ T α) ∧ (∀ t', (∀ α, t' ≤ T α) → t' ≤ t) := by
  let J := {t : TopologicalSpace X // ∀ α, (T α).IsOpen ≤ t.IsOpen}
  let O : J → Set (Set X) := fun t => {s | t.1.IsOpen s}
  have hO : ∀ α, is_topology X (O α) := by
    intro α
    exact ⟨@isOpen_univ X α.1,
      fun s t hs ht => @IsOpen.inter X α.1 s t hs ht,
      fun s hs => @isOpen_sUnion X α.1 s hs⟩
  obtain ⟨O', hO', _⟩ := exercise_13_4b2_assumed X J O hO
  have htop := hO'.1
  simp only [is_topology] at htop
  let t : TopologicalSpace X :=
    TopologicalSpace.mk (fun s => s ∈ O') htop.1 htop.2.1 htop.2.2
  have ht : (∀ α, t ≤ T α) ∧ (∀ t', (∀ α, t' ≤ T α) → t' ≤ t) := by
    constructor
    · intro α
      apply (TopologicalSpace.le_def (t := t) (s := T α)).2
      intro s hs
      change s ∈ O'
      apply hO'.2.2 {s | (T α).IsOpen s}
      · exact ⟨@isOpen_univ X (T α),
          fun u v hu hv => @IsOpen.inter X (T α) u v hu hv,
          fun u hu => @isOpen_sUnion X (T α) u hu⟩
      · intro j
        exact j.2 α
      · exact hs
    · intro t' ht'
      apply (TopologicalSpace.le_def (t := t') (s := t)).2
      intro s hs
      exact hO'.2.1 ⟨t', fun α =>
        (TopologicalSpace.le_def (t := t') (s := T α)).1 (ht' α)⟩ hs
  refine ⟨t, ht, ?_⟩
  intro t' ht'
  exact le_antisymm (ht.2 t' ht'.1) (ht'.2 t ht.1)
