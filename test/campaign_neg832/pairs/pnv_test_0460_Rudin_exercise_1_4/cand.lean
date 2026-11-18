import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {E : Set α} [PartialOrder α] (αE : ∃ a, a ∈ E ∧ ∀ b ∈ E, a ≤ b) (βE : ∃ b, ∀ a ∈ E, a ≤ b) : ∃ a ∈ E, a ≤ b := sorry
