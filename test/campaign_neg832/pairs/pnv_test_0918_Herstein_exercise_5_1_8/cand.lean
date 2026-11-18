import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] {a b : F} {n : ℕ} (hpn : p ^ n = m) : (a + b) ^ m = a ^ m + b ^ m := sorry
