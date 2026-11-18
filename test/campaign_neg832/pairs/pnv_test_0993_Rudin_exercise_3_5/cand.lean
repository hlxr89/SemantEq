import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy {a b : ℕ → ℝ} (ha : BddAbove (Set.range a)) (hb : BddAbove (Set.range b)): limsup (fun n => a n + b n) ≤ limsup a + limsup b := sorry
