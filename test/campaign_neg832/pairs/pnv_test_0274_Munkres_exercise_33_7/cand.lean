import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy [TopologicalSpace X] [T2Space X] (h : ∀ x : X, ∃ s : Set X, IsCompact s ∧ IsOpen s ∧ x ∈ s) : LocallyCompactSpace X := sorry
