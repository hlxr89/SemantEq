import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [PartialOrder X] [TopologicalSpace X] [OrderTopology X] : ∀ (x : X) (s : Set X), IsOpen s → x ∈ s → ∃ (t : Set X), IsOpen t ∧ x ∈ t ∧ Disjoint t s := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_31_3 {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  letI : OrderTopology α := h
  classical
  cases isEmpty_or_nonempty α with
  | inl hα =>
      letI : IsEmpty α := hα
      exact ⟨by
        intro s a hs ha
        exact isEmptyElim a⟩
  | inr hα =>
      letI : Nonempty α := hα
      let x : α := Classical.choice hα
      obtain ⟨t, ht_open, hxt, hts⟩ :=
        dummy_assumed x (Set.univ : Set α) isOpen_univ (Set.mem_univ x)
      exact False.elim (hts.le_bot ⟨hxt, Set.mem_univ x⟩)
