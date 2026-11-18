import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] {A : Set X} {x : X} (hA : IsClosed A) (hxA : x ∈ closure A) (hxXA : x ∉ A) (h : ∀ {U V : Set X}, IsOpen U → IsOpen V → x ∈ U ∩ V → (U ∩ A).Nonempty → (V ∩ Aᶜ).Nonempty → Set.Nonempty (U ∩ V ∩ frontier A)) : x ∈ frontier A := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_6 {X : Type*}
  [TopologicalSpace X] {A C : Set X} (hc : IsConnected C)
  (hCA : C ∩ A ≠ ∅) (hCXA : C ∩ Aᶜ ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ := by
  by_contra hn
  have hempty : C ∩ frontier A = ∅ := hn
  have hsub : C ⊆ interior A ∪ interior Aᶜ := by
    intro x hxC
    have hxnot : x ∉ frontier A := by
      intro hxf
      have hx : x ∈ C ∩ frontier A := ⟨hxC, hxf⟩
      rw [hempty] at hx
      exact hx
    have hxcompl : x ∈ (frontier A)ᶜ := hxnot
    simpa only [compl_frontier_eq_union_interior] using hxcompl
  have hdisj : Disjoint (interior A) (interior Aᶜ) := by
    refine Set.disjoint_left.2 ?_
    intro x hxA hxAc
    exact (interior_subset hxAc) (interior_subset hxA)
  rcases hc.isPreconnected.subset_or_subset isOpen_interior isOpen_interior hdisj hsub with hC | hC
  · rcases Set.nonempty_iff_ne_empty.mpr hCXA with ⟨x, hxC, hxAc⟩
    exact hxAc (interior_subset (hC hxC))
  · rcases Set.nonempty_iff_ne_empty.mpr hCA with ⟨x, hxC, hxA⟩
    exact (interior_subset (hC hxC)) hxA
