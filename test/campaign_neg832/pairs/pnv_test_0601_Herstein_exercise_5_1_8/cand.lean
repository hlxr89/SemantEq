import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] {m : ℕ} (hmn : m = p ^ n) (a b : F) (n : ℕ) : (a + b) ^ m = a ^ m + b ^ m := sorry
