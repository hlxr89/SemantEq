import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (n : ℕ) (hn : Nat.Prime n) (hn3 : 3 < n) : Irreducible (2 : ℤ√(-n)) ∧ Irreducible (1 : ℤ√(-n)) := sorry
