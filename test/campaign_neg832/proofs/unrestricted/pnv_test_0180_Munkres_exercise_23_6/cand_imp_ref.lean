import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] {A : Set X} {C : Set X} (hC : IsConnected C) (hAC : C ∩ A ≠ ∅) (hCc : C ∩ (frontier A) ≠ ∅) : C ∩ (frontier A) ≠ ∅ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_6 {X : Type*}
  [TopologicalSpace X] {A C : Set X} (hc : IsConnected C)
  (hCA : C ∩ A ≠ ∅) (hCXA : C ∩ Aᶜ ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ := by
  by_contra hfrontier
  have hCsub : C ⊆ (frontier A)ᶜ :=
    (Set.disjoint_iff_inter_eq_empty.mpr hfrontier).subset_compl_right
  rw [compl_frontier_eq_union_interior] at hCsub
  have hdisj : Disjoint (interior A) (interior Aᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  rcases hc.isPreconnected.subset_or_subset isOpen_interior isOpen_interior hdisj hCsub with hA | hAc
  · obtain ⟨x, hxC, hxAc⟩ := Set.nonempty_iff_ne_empty.mpr hCXA
    exact hxAc (interior_subset (hA hxC))
  · obtain ⟨x, hxC, hxA⟩ := Set.nonempty_iff_ne_empty.mpr hCA
    exact (interior_subset (hAc hxC)) hxA
