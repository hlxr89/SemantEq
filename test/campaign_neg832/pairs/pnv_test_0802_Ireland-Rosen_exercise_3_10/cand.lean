import Mathlib

open Real
open scoped BigOperators

theorem dummy (n : ℕ) (h : n ≠ 0) (h' : ¬ Prime n) : (Nat.factorial n % n) = 0 := sorry
