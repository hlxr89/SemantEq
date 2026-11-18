import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] [T2Space X] {A : Set X} {C : Set X} (hC : IsConnected C) (hCA : C ∩ A ≠ ∅) (hCA' : C ∩ (frontier A) ≠ ∅) : C ∩ (frontier A) ≠ ∅ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_6 {X : Type*}
  [TopologicalSpace X] {A C : Set X} (hc : IsConnected C)
  (hCA : C ∩ A ≠ ∅) (hCXA : C ∩ Aᶜ ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ := by
  intro hfrontier
  have hdis : Disjoint C (frontier A) :=
    Set.disjoint_iff_inter_eq_empty.mpr hfrontier
  have hsub : C ⊆ (frontier A)ᶜ := by
    intro x hxC hxfrontier
    exact Set.disjoint_left.1 hdis hxC hxfrontier
  rw [compl_frontier_eq_union_interior] at hsub
  have hopen_disjoint : Disjoint (interior A) (interior Aᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  rcases hc.isPreconnected.subset_or_subset isOpen_interior isOpen_interior
      hopen_disjoint hsub with hA | hAc
  · rcases Set.nonempty_iff_ne_empty.mpr hCXA with ⟨x, hxC, hxAc⟩
    exact hxAc (interior_subset (hA hxC))
  · rcases Set.nonempty_iff_ne_empty.mpr hCA with ⟨x, hxC, hxA⟩
    exact (interior_subset (hAc hxC)) hxA
