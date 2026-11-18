import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_32_2c_assumed
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X : Type*} [TopologicalSpace X] {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)] (hX : NormalSpace (∀ i, π i)) (i : ι) [Nonempty (π i)] : NormalSpace (π i) := by
  -- not proved: the antecedent requires every factor to be nonempty, but the goal assumes only the selected factor is nonempty
  sorry
