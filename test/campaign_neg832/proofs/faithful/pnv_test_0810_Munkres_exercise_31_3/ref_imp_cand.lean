import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_31_3_assumed {α : Type*} [PartialOrder α]
  [TopologicalSpace α] (h : OrderTopology α) : RegularSpace α := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {α : Type u} [PartialOrder α] [t : TopologicalSpace α] [t' : OrderTopology α] : T2Space α := by
  -- not proved: RegularSpace does not imply T2Space without a separation axiom
  sorry
