import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {p : ℕ} [hp : Fact (Nat.Prime p)] {k : ℕ} {hk : Nat.Prime (p ^ (k + 1))} {x : ℤ} (hle : x ^ (p ^ (k + 1)) = 1) : ∃ (m : ℕ), 0 < m ∧ m < p ^ (k + 1) ∧ x ^ m = 1 := sorry
