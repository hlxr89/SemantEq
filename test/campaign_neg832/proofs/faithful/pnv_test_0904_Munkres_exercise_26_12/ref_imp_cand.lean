import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_26_12_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (h : Function.Surjective p) (hc : Continuous p)
  (hp : IsClosedMap p) (hp : ∀ y, IsCompact (p ⁻¹' {y}))
  (hY : CompactSpace Y) : CompactSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] [T2Space X] (p : X → Y) (hc : Continuous p) (hs : Function.Surjective p) (hk : ∀ y : Y, IsCompact (p ⁻¹' {y})) : CompactSpace X := by
  -- not proved: the candidate omits IsClosedMap p and is false for a continuous bijection from an infinite discrete space to the same set with the compact cofinite topology
  sorry
