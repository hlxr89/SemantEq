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
  let t : I → TopologicalSpace X := fun i =>
    { IsOpen := fun s => s ∈ T i
      isOpen_univ := (h i).1
      isOpen_inter := (h i).2.1
      isOpen_sUnion := (h i).2.2 }
  obtain ⟨m, hm, hleast⟩ := dummy_assumed X t
  let M : Set (Set X) := {s | m.IsOpen s}
  have hM : is_topology X M :=
    ⟨m.isOpen_univ, m.isOpen_inter, m.isOpen_sUnion⟩
  have hsub : ∀ i, M ⊆ T i := by
    intro i s hs
    exact hm i s hs
  have hgreatest : ∀ T'', is_topology X T'' → (∀ i, T'' ⊆ T i) → T'' ⊆ M := by
    intro T'' hT'' hTsub
    let t'' : TopologicalSpace X :=
      { IsOpen := fun s => s ∈ T''
        isOpen_univ := hT''.1
        isOpen_inter := hT''.2.1
        isOpen_sUnion := hT''.2.2 }
    exact hleast t'' (fun i _ hs => hTsub i hs)
  refine ⟨M, ⟨hM, hsub, hgreatest⟩, ?_⟩
  intro M' hM'
  apply Set.Subset.antisymm
  · exact hgreatest M' hM'.1 hM'.2.1
  · exact hM'.2.2 M hM hsub
