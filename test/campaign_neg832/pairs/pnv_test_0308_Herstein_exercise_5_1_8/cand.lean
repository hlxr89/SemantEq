import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] {p : ℕ} (hp : CharP F p) {n : ℕ} (hn : 0 < n) (a b : F) : (a + b)^(p^n) = a^(p^n) + b^(p^n) := sorry
