import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {s : Set ℝ} (hs : IsOpen s) : ∃ t : Set (Set ℝ), t.Countable ∧ s = ⋃₀ t ∧ ∀ a b, a ∈ t → b ∈ t → a ≠ b → Disjoint a b := sorry
