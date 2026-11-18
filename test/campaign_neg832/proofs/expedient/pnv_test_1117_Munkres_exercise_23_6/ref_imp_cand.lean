import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_23_6_assumed {X : Type*}
  [TopologicalSpace X] {A C : Set X} (hc : IsConnected C)
  (hCA : C ∩ A ≠ ∅) (hCXA : C ∩ Aᶜ ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} [TopologicalSpace X] {A : Set X} {C : Set X} (hA : IsConnected C) (hAC : C ∩ A ≠ ∅) (hAC' : C ∩ closure Aᶜ ≠ ∅) : C ∩ @frontier X _ A ≠ ∅ := by
  by_contra h
  have hsub : C ⊆ interior A ∪ interior Aᶜ := by
    intro x hx
    have hx' : x ∉ frontier A := by
      intro hxf
      have : x ∈ C ∩ frontier A := ⟨hx, hxf⟩
      rw [h] at this
      exact this
    simpa only [← compl_frontier_eq_union_interior, mem_compl_iff] using hx'
  have hleft : (C ∩ interior A).Nonempty := by
    rcases Set.nonempty_iff_ne_empty.mpr hAC with ⟨x, hxC, hxA⟩
    refine ⟨x, hxC, ?_⟩
    by_contra hxi
    have hxf : x ∈ frontier A := by
      rw [frontier]
      exact ⟨subset_closure hxA, hxi⟩
    have : x ∈ C ∩ frontier A := ⟨hxC, hxf⟩
    rw [h] at this
    exact this
  have hright : (C ∩ interior Aᶜ).Nonempty := by
    rcases Set.nonempty_iff_ne_empty.mpr hAC' with ⟨x, hxC, hxA⟩
    refine ⟨x, hxC, ?_⟩
    by_contra hxi
    have hxcl : x ∈ closure A := by
      simpa only [interior_compl, mem_compl_iff, not_not] using hxi
    have hxf : x ∈ frontier A := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨hxcl, hxA⟩
    have : x ∈ C ∩ frontier A := ⟨hxC, hxf⟩
    rw [h] at this
    exact this
  rcases hA.isPreconnected (interior A) (interior Aᶜ) isOpen_interior isOpen_interior
      hsub hleft hright with ⟨x, _, hxA, hxAc⟩
  exact (interior_subset hxAc) (interior_subset hxA)
