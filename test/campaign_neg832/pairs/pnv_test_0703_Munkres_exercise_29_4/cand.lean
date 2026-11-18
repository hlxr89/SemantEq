import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} [Fintype ι] [Nonempty ι] : ¬LocallyCompactSpace (Units (ι → ℝ)) := sorry
