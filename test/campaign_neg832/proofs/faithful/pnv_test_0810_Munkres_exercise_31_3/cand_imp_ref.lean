import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {α : Type u} [PartialOrder α] [t : TopologicalSpace α] [t' : OrderTopology α] : T2Space α := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_31_3 {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  -- not proved: T2Space does not imply RegularSpace, and no applicable order-topology bridge exists
  sorry
