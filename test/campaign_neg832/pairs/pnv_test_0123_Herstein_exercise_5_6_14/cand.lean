import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] {p n : ℕ} [hf : CharP F p] : ∀ m : ℕ, m = p^n → ∀ x y : F, x^m = x → y^m = y → x = y := sorry
