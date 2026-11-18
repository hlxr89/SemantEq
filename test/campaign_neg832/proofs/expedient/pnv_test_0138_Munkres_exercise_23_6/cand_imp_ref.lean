import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] (A : Set X) (C : Set X) (hC : IsConnected C) (hAC : C ∩ (frontier A) ≠ ∅) : C ∩ (frontier A) ≠ ∅ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_6 {X : Type*}
  [TopologicalSpace X] {A C : Set X} (hc : IsConnected C)
  (hCA : C ∩ A ≠ ∅) (hCXA : C ∩ Aᶜ ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ := by
  intro hEmpty
  have hsub : C ⊆ interior A ∪ interior Aᶜ := by
    intro x hxC
    have hxnf : x ∉ frontier A := by
      intro hxf
      have hx : x ∈ C ∩ frontier A := ⟨hxC, hxf⟩
      rw [hEmpty] at hx
      exact hx
    by_cases hxA : x ∈ interior A
    · exact Or.inl hxA
    · apply Or.inr
      rw [interior_compl]
      intro hxcl
      apply hxnf
      rw [frontier]
      exact ⟨hxcl, hxA⟩
  have hd : Disjoint (interior A) (interior Aᶜ) := by
    rw [Set.disjoint_left]
    intro x hxA hxAc
    exact interior_subset hxAc (interior_subset hxA)
  rcases hc.isPreconnected.subset_or_subset isOpen_interior isOpen_interior hd hsub with hCi | hCic
  · rcases Set.nonempty_iff_ne_empty.mpr hCXA with ⟨x, hxC, hxAc⟩
    exact hxAc (interior_subset (hCi hxC))
  · rcases Set.nonempty_iff_ne_empty.mpr hCA with ⟨x, hxC, hxA⟩
    exact interior_subset (hCic hxC) hxA
