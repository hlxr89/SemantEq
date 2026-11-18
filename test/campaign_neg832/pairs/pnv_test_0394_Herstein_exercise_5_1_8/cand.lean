import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (F : Type*) [Field F] (p : ℕ) [hp : Fact (Nat.Prime p)] (m : ℕ) (hmp : m = p ^ n) (a b : F) : (a + b)^m = a^m + b^m := sorry
