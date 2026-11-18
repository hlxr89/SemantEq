import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] {p : ℕ} {n : ℕ} [hp : Fact (Nat.Prime p)] [CharP F p] (a b : F) : (a + b)^(p ^ n) = a^(p^n) + b^(p^n) := sorry
