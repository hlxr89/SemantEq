import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] {m : ℕ} (hmn : m = p ^ n) : ∀ (x : F), x ≠ 1 → ∃! y, y ^ m = x ∧ y ≠ 1 := sorry
