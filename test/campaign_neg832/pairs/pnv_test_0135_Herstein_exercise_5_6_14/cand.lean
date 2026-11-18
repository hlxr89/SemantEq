import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] (p : ℕ) [hp : Fact (Nat.Prime p)] [CharP F p] (n : ℕ) : (∃ (x : F), x ^ (p ^ n) = x) → (∀ x y : F, x ≠ y → x ^ (p ^ n) ≠ y ^ (p ^ n)) := sorry
