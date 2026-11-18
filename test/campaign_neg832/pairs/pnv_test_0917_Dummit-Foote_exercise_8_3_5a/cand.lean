import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (n : ℕ) [Fact (2 < n)] [Fact (Nat.Prime n)] : Irreducible (4 * (n - 1) - 1 : ZMod (4 * (n - 1) - 1)) := sorry
