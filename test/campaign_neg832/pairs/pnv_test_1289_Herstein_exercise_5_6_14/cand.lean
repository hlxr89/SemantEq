import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] {p : ℕ} [CharP F p] (n : ℕ) [Fact (p = 0 ∨ p = 1 ∨ p ≠ 1)] (hp : p = 0 ∨ p = 1 ∨ p ≠ 1) : IsCyclic (Multiplicative (ZMod (p ^ n))) := sorry
