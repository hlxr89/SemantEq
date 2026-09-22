import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- Both statements use only Mathlib vocabulary (OrderTopology, OrderClosedTopology,
-- Continuous, min); neither side has local defs, so the unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem min_continuous_orderClosed_assumed {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [LinearOrder Y] [OrderClosedTopology Y] (f g : X → Y)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => min (f x) (g x)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_18_8b {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LinearOrder Y] [OrderTopology Y] {f g : X → Y}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (λ x => min (f x) (g x)) := by
  -- an order topology has a closed order relation, so the candidate statement
  -- applies to Y directly
  exact min_continuous_orderClosed_assumed f g hf hg
