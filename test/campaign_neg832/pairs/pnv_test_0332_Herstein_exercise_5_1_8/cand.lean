import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] {p : ℕ} [hp : Fact p.Prime] (hF : CharP F p) (m : ℕ) (hpm : p ^ m ≠ 0) (a b : F) : (a + b) ^ p ^ m = a ^ p ^ m + b ^ p ^ m := sorry
