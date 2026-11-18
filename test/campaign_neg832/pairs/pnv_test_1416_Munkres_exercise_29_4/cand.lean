import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {ι : Type*} [Infinite ι] : ¬LocallyCompactSpace (Π (i : ι), Icc (0 : ℝ) 1) := sorry
