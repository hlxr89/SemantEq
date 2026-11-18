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
theorem dummy {ι : Type*} {X : ι → Type*} [Π α, TopologicalSpace (X α)] (h : NormalSpace (Π α, X α)) (α : ι) [ne : Nonempty (X α)] : NormalSpace (X α) := by
  -- not proved: the candidate permits another factor to be empty, making the product normal without forcing the selected nonempty factor to be normal
  sorry
