import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (s : Set ℝ) (hs : IsOpen s) : s = ⋃ (x ∈ s) (y ∈ s), Set.Ioo x y := sorry
