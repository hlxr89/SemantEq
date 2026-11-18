import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {n : ℕ} (hn : n > 3 ∧ Nat.Prime n) (a : ℤ√(-n)) (ha : a ≠ 0) : Irreducible a := sorry
