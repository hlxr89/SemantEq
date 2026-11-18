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
theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (hp : Continuous p) (hps : IsClosed (range p)) (hps_inv : ∀ y : Y, IsCompact (p ⁻¹' {y})) (hY : CompactSpace Y) : CompactSpace X := by
  -- not proved: a closed range does not imply that p is a closed map, and the statement is false in general
  sorry
