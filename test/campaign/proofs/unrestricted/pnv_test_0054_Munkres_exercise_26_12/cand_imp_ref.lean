import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : Continuous p) (hpc : IsClosedMap p) (hps : Function.Surjective p) (hpf : ∀ y : Y, IsCompact (p ⁻¹' {y})) (hY : CompactSpace Y) : CompactSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_26_12 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (h : Function.Surjective p) (hc : Continuous p)
  (hp : IsClosedMap p) (hp : ∀ y, IsCompact (p ⁻¹' {y}))
  (hY : CompactSpace Y) : CompactSpace X := by
  exact dummy_assumed p hc (by assumption) h (by assumption) hY
