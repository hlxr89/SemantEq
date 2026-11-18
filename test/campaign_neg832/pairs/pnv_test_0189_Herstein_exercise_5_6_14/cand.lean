import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p] (n : ℕ) : ∀ x y : F, (x ^ (p ^ n) = x) → (y ^ (p ^ n) = y) → x = y → x = y := sorry
