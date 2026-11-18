import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {n : ℕ} (hn : n > 3 ∧ Nat.Prime n) : Irreducible (Polynomial.cyclotomic (2*(n+1)) ℤ) := sorry
