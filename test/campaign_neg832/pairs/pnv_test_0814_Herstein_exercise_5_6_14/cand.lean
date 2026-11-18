import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] (m : ℕ) (hpm : m = p ^ n) : ∀ (x : F), x ≠ 1 → x ^ m ≠ x → x ≠ 0 → x ^ m - x ≠ 0 := sorry
