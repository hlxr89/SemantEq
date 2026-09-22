import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (p : ℕ) [Fact (Nat.Prime p)] (a : ℤ) : a ^ p ≡ a [ZMOD p] := sorry
