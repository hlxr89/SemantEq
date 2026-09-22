import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [TopologicalSpace X] {ι : Type*} {A : ι → Set X} (hA : ∀ i, IsConnected (A i)) {U : Set X} (hU : IsConnected U) (h : ∀ i, (A i ∩ U).Nonempty) : IsConnected (U ∪ ⋃ i, A i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_3 {X α : Type*} [TopologicalSpace X]
  {A : α → Set X}
  (hAa : ∀ a, IsConnected (A a))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ a, A₀ ∩ A a ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ a, A a)) := by
  apply dummy_assumed hAa hA
  intro a
  rw [inter_comm]
  exact nonempty_iff_ne_empty.mpr (h a)
