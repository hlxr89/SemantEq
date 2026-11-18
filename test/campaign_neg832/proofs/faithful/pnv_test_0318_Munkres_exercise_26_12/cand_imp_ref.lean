import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] (hX : T2Space X) (p : X → Y) (h_cont : Continuous p) (h_surj : Function.Surjective p) (h_closed : IsClosedMap p) (h_compact_fibers : ∀ y : Y, IsCompact (p ⁻¹' {y})) : CompactSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_26_12 {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (p : X → Y) (h : Function.Surjective p) (hc : Continuous p)
  (hp : IsClosedMap p) (hp : ∀ y, IsCompact (p ⁻¹' {y}))
  (hY : CompactSpace Y) : CompactSpace X := by
  let originalTopology : TopologicalSpace X := inferInstance
  letI : TopologicalSpace X := ⊥
  letI : DiscreteTopology X := discreteTopology_bot X
  haveI : CompactSpace X :=
    dummy_assumed X X (by infer_instance) id continuous_id Function.surjective_id
      IsClosedMap.id (fun y ↦ isCompact_singleton)
  haveI : Finite X := finite_of_compact_of_discrete
  letI : TopologicalSpace X := originalTopology
  exact inferInstance
