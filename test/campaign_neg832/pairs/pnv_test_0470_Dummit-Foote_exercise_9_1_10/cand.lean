import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy : ∃ (P : ℕ → Ideal (Polynomial (ℤ))), (∀ n, Ideal.IsPrime (P n)) ∧ (∀ n m, n ≠ m → P n ≠ P m) := sorry
