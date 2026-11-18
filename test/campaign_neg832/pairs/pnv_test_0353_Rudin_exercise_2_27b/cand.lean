import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {E : Set (EuclideanSpace ℝ (Fin k))} (hE : Set.Infinite E) : ∃ (P : Set (EuclideanSpace ℝ (Fin k))), Set.Countable (P \ E) := sorry
