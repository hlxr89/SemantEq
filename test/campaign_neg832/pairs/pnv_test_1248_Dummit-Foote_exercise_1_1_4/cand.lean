import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (n : ℕ) (a b c : ℕ) (ha : a ≠ 0) (h : a * b ≡ a * c [MOD n]) : b ≡ c [MOD n] := sorry
