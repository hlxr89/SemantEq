import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem dummy (R : Type*) [Ring R] {x : R} (hx : x ≠ 0) : ∀ {y : R}, y ≠ 0 → x * y ≠ 0 := sorry
