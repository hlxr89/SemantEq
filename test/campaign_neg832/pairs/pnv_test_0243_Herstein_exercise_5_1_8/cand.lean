import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] {p : ℕ} (h_char : p ≠ 0) (n : ℕ) (a b : F) (m : ℕ) (h_m : m = p ^ n) : (a + b) ^ m = (a ^ m) + (b ^ m) := sorry
