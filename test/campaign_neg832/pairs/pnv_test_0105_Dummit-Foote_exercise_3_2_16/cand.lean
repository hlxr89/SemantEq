import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (p : ℕ) [hp : Fact p.Prime] (a : ℕ) : a ^ p ≡ a [MOD p] := sorry
