import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] (A : Set X) (C : Set X) (hC : IsConnected C) (hAC : C ∩ A ≠ ∅) (hCc : C ∩ closure (C \ A) ≠ ∅) : C ∩ closure (C ∩ (closure A ∩ closure (C \ A))) ≠ ∅ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_6 {X : Type*}
  [TopologicalSpace X] {A C : Set X} (hc : IsConnected C)
  (hCA : C ∩ A ≠ ∅) (hCXA : C ∩ Aᶜ ≠ ∅) :
  C ∩ (frontier A) ≠ ∅ := by
  have hCA' : (C ∩ closure A).Nonempty :=
    (nonempty_iff_ne_empty.mpr hCA).mono (inter_subset_inter_right C subset_closure)
  have hCXA' : (C ∩ closure Aᶜ).Nonempty :=
    (nonempty_iff_ne_empty.mpr hCXA).mono (inter_subset_inter_right C subset_closure)
  have hsub : C ⊆ closure A ∪ closure Aᶜ := by
    intro x hx
    by_cases hxa : x ∈ A
    · exact Or.inl (subset_closure hxa)
    · exact Or.inr (subset_closure hxa)
  rw [frontier_eq_closure_inter_closure]
  exact (isPreconnected_closed_iff.mp hc.isPreconnected
    (closure A) (closure Aᶜ) isClosed_closure isClosed_closure hsub hCA' hCXA').ne_empty
