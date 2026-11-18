import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} (h : Nat.Prime p ∧ ∃ (n : ℕ), p = 2^n + 1) : IsPrimitiveRoot 3 p := sorry
