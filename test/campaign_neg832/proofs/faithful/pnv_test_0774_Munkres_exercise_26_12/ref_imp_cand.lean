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
theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y] (f : X → Y) (hf : Continuous f) (hf2 : Function.Surjective f) (hf3 : ∀ y : Y, IsCompact (f⁻¹' {y}) ) : CompactSpace X := by
  -- not proved: the goal hypotheses do not imply the IsClosedMap hypothesis required by the antecedent
  sorry
