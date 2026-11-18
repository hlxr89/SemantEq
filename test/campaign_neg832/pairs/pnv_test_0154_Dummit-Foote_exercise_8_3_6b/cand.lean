import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (q : ℕ) [Fact (Nat.Prime q)] (hq : q % 4 = 3) : Fintype.card (ZMod q) = q^2 := sorry
