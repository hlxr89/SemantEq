import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X : Type*} [MetricSpace X] [CompactSpace X] (h : Continuous fun x : X => (0 : ℝ)) : ¬LocallyCompactSpace X := sorry
