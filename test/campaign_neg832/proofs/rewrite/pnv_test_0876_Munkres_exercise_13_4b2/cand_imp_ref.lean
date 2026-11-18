import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} (T : ι → TopologicalSpace X) : ∃! t : TopologicalSpace X, (∀ α, t ≤ T α) ∧ (∀ t', (∀ α, t' ≤ T α) → t' ≤ t) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_13_4b2 (X I : Type*) (T : I → Set (Set X)) (h : ∀ i, is_topology X (T i)) :
  ∃! T', is_topology X T' ∧ (∀ i, T' ⊆ T i) ∧
  ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ T' := by
  let τ : I → TopologicalSpace X := fun i =>
    TopologicalSpace.mk (fun s => s ∈ T i) (h i).1 (h i).2.1 (h i).2.2
  let J := {t : TopologicalSpace X // ∀ i, t.IsOpen ≤ (τ i).IsOpen}
  obtain ⟨t, ht, _⟩ := dummy_assumed (fun j : J => j.1)
  let O : Set (Set X) := {s | @IsOpen X t s}
  have hO : is_topology X O ∧ (∀ i, O ⊆ T i) ∧
      ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ O := by
    refine ⟨?_, ?_, ?_⟩
    · exact ⟨@isOpen_univ X t,
        fun s u hs hu => @IsOpen.inter X t s u hs hu,
        fun s hs => @isOpen_sUnion X t s hs⟩
    · intro i
      have hτ : τ i ≤ t := ht.2 (τ i) (fun j =>
        (TopologicalSpace.le_def (t := τ i) (s := j.1)).2 (j.2 i))
      exact (TopologicalSpace.le_def (t := τ i) (s := t)).1 hτ
    · intro T'' hT'' hsub
      let t'' : TopologicalSpace X :=
        TopologicalSpace.mk (fun s => s ∈ T'') hT''.1 hT''.2.1 hT''.2.2
      let j : J := ⟨t'', fun i => hsub i⟩
      exact (TopologicalSpace.le_def (t := t) (s := j.1)).1 (ht.1 j)
  refine ⟨O, hO, ?_⟩
  intro O' hO'
  exact Set.Subset.antisymm
    (hO.2.2 O' hO'.1 hO'.2.1)
    (hO'.2.2 O hO.1 hO.2.1)
