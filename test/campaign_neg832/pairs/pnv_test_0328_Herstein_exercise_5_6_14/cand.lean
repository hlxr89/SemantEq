import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] (m : ℕ) (hn : m = p ^ n) : ∀ (x : F), x ^ m ≠ x → x ≠ (x ^ p) ^ n := sorry
