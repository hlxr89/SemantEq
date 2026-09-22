import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LinearOrder Y] [OrderClosedTopology Y] (f g : X → Y) (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => min (f x) (g x)) := sorry
