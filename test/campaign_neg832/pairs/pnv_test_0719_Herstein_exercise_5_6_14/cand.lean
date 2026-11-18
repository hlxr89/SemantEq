import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (F : Type*) [Field F] (p : ℕ) [hF : CharP F p] (m : ℕ) (h : Fact (p ≠ 0) ∧ m = p ^ n) : (∃ x : F, x ^ m - x = 0) → (∀ (x y : F), x ^ m - x = 0 ∧ y ^ m - y = 0 → x = y) := sorry
