import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (U : Set ℝ) (hU : IsOpen U) : ∃ (I : Set (Set ℝ)), (∀ i ∈ I, ∃ a b : ℝ, i = Set.Ioo a b) ∧ Countable I ∧ U = ⋃₀ I := sorry
