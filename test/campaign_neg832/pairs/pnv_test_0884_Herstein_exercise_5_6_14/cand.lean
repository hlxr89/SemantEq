import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy (F : Type*) [Field F] [hF : CharP F p] (m : ℕ) (h : m = p^n) : (∀ (x : F), x^m = x → x = 0) ∧ (∀ (x : F), x^(m-1) = 1 → x = 1) := sorry
