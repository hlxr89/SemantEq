import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (q : ℕ) [Fact (q.Prime)] (hq : q ≡ 3 [MOD 4]) : Fintype.card (ZMod q) = q^2 := sorry
