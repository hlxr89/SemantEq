import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (a b : ℕ → ℝ) : limsup (a + b) ≤ limsup a + limsup b := sorry
