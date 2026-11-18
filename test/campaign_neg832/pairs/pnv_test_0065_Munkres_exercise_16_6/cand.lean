import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {r r1 r2 : ℚ} (hr1 : r1 < r) (hr2 : r2 < r) : ∃ (q : ℚ × ℚ), (r1, r2) ∈ Set.Icc q (r, r) := sorry
