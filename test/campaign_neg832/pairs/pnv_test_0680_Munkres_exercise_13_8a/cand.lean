import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy : TopologicalSpace.IsTopologicalBasis (Set.range fun p : ℚ × ℚ => Ioo p.1 p.2) := sorry
