import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)] [∀ i, CompactSpace (π i)] [∀ i, Nonempty (π i)] (h : NormalSpace (∀ i, π i)) : ∀ i, NormalSpace (π i) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_32_2c
  {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
  (h : ∀ i, Nonempty (X i)) (h2 : NormalSpace (Π i, X i)) :
  ∀ i, NormalSpace (X i) := by
  -- not proved: dummy_assumed requires CompactSpace instances for every X i, which the goal does not assume
  sorry
