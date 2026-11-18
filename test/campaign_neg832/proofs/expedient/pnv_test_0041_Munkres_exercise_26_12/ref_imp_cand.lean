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
theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (h : CompactSpace Y) (h' : Continuous p) (h'' : Function.Surjective p) (hc : ∀ y : Y, IsCompact (p ⁻¹' {y})) : CompactSpace X := by
  -- not proved: false without a closed-map hypothesis; an infinite discrete space maps continuously and bijectively to an infinite indiscrete compact space.
  sorry
