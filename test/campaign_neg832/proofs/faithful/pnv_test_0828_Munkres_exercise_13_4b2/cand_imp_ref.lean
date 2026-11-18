import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
def is_topology (X : Type*) (T : Set (Set X)) :=
  univ ∈ T ∧
  (∀ s t, s ∈ T → t ∈ T → s ∩ t ∈ T) ∧
  (∀s, (∀t ∈ s, t ∈ T) → sUnion s ∈ T)

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (X : Type u) (T : ι → TopologicalSpace X) : ∃ (m : TopologicalSpace X), (∀ i, T i ≤ m) ∧ ∀ (t : TopologicalSpace X) (h : ∀ i, T i ≤ t), m ≤ t := by
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
  obtain ⟨m, hm, hmin⟩ := dummy_assumed X τ
  let O : Set (Set X) := {s | @IsOpen X m s}
  have hOtop : is_topology X O :=
    ⟨isOpen_univ, fun s t hs ht => m.isOpen_inter s t hs ht,
      fun s hs => m.isOpen_sUnion s hs⟩
  have hOsub : ∀ i, O ⊆ T i := by
    intro i
    exact TopologicalSpace.le_def.mp (hm i)
  have hOmax : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ O := by
    intro T'' hT'' hsub
    let t : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    exact TopologicalSpace.le_def.mp
      (hmin t (fun i => TopologicalSpace.le_def.mpr (hsub i)))
  refine ⟨O, ⟨hOtop, hOsub, hOmax⟩, ?_⟩
  intro O' hO'
  apply Set.Subset.antisymm
  · exact hOmax O' hO'.1 hO'.2.1
  · exact hO'.2.2 O hOtop hOsub
