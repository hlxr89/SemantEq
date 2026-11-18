import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] (n : ℕ) (hpn : p^n ≠ 0) : ∀ x : F, x ≠ 1 → x^(p^n) ≠ x := sorry
