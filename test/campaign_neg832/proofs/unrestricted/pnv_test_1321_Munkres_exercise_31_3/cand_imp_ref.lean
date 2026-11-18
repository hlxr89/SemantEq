import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] : T2Space α := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_31_3 {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  -- not proved: the claim is false for partial orders; the linear-order antecedent cannot imply it
  sorry
