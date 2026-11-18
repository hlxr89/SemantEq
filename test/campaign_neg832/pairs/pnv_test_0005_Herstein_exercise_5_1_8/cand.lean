import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [Fintype F] (hp : Fintype.card F = q) (m : ℕ) (hq : q = p ^ n) (a b : F) : (a + b) ^ m = a ^ m + b ^ m := sorry
