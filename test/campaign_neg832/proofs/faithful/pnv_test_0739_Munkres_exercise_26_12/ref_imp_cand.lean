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
theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (p : X → Y) (hp : Continuous p) (hps : ∀ y, IsCompact (p ⁻¹' {y} : Set X)) (hY : CompactSpace Y) : CompactSpace X := by
  -- not proved: the candidate omits the surjectivity and closed-map hypotheses required by the assumed statement
  sorry
