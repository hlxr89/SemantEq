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
  intro hempty
  have hdisj : Disjoint C (frontier A) := Set.disjoint_left.2 (by
    intro x hxC hxf
    have hx : x ∈ C ∩ frontier A := ⟨hxC, hxf⟩
    rw [hempty] at hx
    exact hx)
  have huv : Disjoint (interior A) (interior Aᶜ) := Set.disjoint_left.2 (by
    intro x hxA hxAc
    exact (interior_subset hxAc) (interior_subset hxA))
  have hsub : C ⊆ interior A ∪ interior Aᶜ := by
    intro x hxC
    by_cases hxA : x ∈ interior A
    · exact Or.inl hxA
    · right
      rw [interior_compl]
      intro hxcl
      apply Set.disjoint_left.1 hdisj hxC
      rw [frontier]
      exact ⟨hxcl, hxA⟩
  rcases hc.isPreconnected.subset_or_subset isOpen_interior isOpen_interior huv hsub with h | h
  · rcases Set.nonempty_iff_ne_empty.mpr hCXA with ⟨x, hxC, hxAc⟩
    exact hxAc (interior_subset (h hxC))
  · rcases Set.nonempty_iff_ne_empty.mpr hCA with ⟨x, hxC, hxA⟩
    exact (interior_subset (h hxC)) hxA
