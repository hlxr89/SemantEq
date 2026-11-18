import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hpm : p^n = m) (z : F) : z ^ m - z = 0 ↔ z = 0 ∨ z ^ p = z := sorry
