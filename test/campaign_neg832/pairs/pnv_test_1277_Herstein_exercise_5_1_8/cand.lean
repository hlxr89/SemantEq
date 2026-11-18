import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] (p_neq_zero : p ≠ 0) {m : ℕ} (h_m : m = p^n) (a b : F) : (a + b) ^ m = a ^ m + b ^ m := sorry
