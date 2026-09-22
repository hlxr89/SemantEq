import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (p : ℕ) [hp : Fact p.Prime] (a : ℤ) : a^p ≡ a [ZMOD p] := sorry
