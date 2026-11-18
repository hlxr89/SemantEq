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
  intro h
  have hs : C ⊆ interior A ∪ interior Aᶜ := by
    rw [← compl_frontier_eq_union_interior]
    intro x hxC hxF
    have : x ∈ C ∩ frontier A := ⟨hxC, hxF⟩
    rw [h] at this
    exact this
  have hd : Disjoint (interior A) (interior Aᶜ) :=
    disjoint_compl_right.mono interior_subset interior_subset
  rcases hc.isPreconnected.subset_or_subset isOpen_interior isOpen_interior hd hs with h | h
  · rcases Set.nonempty_iff_ne_empty.mpr hCXA with ⟨x, hxC, hxA⟩
    exact hxA (interior_subset (h hxC))
  · rcases Set.nonempty_iff_ne_empty.mpr hCA with ⟨x, hxC, hxA⟩
    exact (interior_subset (h hxC)) hxA
