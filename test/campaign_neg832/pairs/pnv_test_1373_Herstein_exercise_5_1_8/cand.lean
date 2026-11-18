import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] (p : ℕ) [CharP F p] (a b : F) (n : ℕ) : (a + b) ^ (p ^ n) = a ^ (p ^ n) + b ^ (p ^ n) := sorry
