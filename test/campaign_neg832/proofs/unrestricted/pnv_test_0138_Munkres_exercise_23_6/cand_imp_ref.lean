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
  rw [← Set.nonempty_iff_ne_empty]
  rw [← Set.nonempty_iff_ne_empty] at hCA hCXA
  by_contra hfront
  have hsep := hc.isPreconnected (closure A)ᶜ (closure Aᶜ)ᶜ
    isClosed_closure.isOpen_compl isClosed_closure.isOpen_compl
  have hcover : C ⊆ (closure A)ᶜ ∪ (closure Aᶜ)ᶜ := by
    intro x hxC
    by_cases hxA : x ∈ closure A
    · right
      intro hxAc
      apply hfront
      refine ⟨x, hxC, ?_⟩
      rw [frontier_eq_closure_inter_closure]
      exact ⟨hxA, hxAc⟩
    · left
      exact hxA
  have hu : (C ∩ (closure A)ᶜ).Nonempty := by
    rcases hCXA with ⟨x, hxC, hxAc⟩
    refine ⟨x, hxC, ?_⟩
    intro hxA
    apply hfront
    refine ⟨x, hxC, ?_⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨hxA, subset_closure hxAc⟩
  have hv : (C ∩ (closure Aᶜ)ᶜ).Nonempty := by
    rcases hCA with ⟨x, hxC, hxA⟩
    refine ⟨x, hxC, ?_⟩
    intro hxAc
    apply hfront
    refine ⟨x, hxC, ?_⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hxA, hxAc⟩
  rcases hsep hcover hu hv with ⟨x, hxC, hxA, hxAc⟩
  by_cases hx : x ∈ A
  · exact hxA (subset_closure hx)
  · exact hxAc (subset_closure hx)
