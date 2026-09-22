import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] (p_neq_0 : p ≠ 0) (a b : F) (n : ℕ) (hn : n ≠ 0) : (a + b) ^ (p ^ n) = a ^ (p ^ n) + b ^ (p ^ n) := sorry
