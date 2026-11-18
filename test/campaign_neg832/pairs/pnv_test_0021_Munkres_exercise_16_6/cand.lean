import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (hX : SecondCountableTopology X) (hY : SecondCountableTopology Y) : ∃ (b : Set (Set (X × Y))), b.Countable ∧ (TopologicalSpace.IsTopologicalBasis b) := sorry
