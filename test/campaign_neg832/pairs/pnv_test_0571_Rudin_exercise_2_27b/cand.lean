import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (E : Set ℝ) [hs : Uncountable E] : Set.Countable (frontier E \ E) := sorry
