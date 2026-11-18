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
theorem dummy {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α] : T2Space α := by
  letI : RegularSpace α := exercise_31_3_assumed (inferInstance : OrderTopology α)
  rw [t2Space_iff_disjoint_nhds]
  intro x y hxy
  simpa only [nhdsSet_singleton] using
    (RegularSpace.regular (isClosed_singleton : IsClosed ({y} : Set α)) (by simpa using hxy)).symm
