import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] [CharP F p] {m : ℕ} (hm : m = p ^ n) : ∀ (x : F), x ≠ 1 → x ^ m ≠ x → x ^ m ≠ 1 → ∃ y : F, (y ^ m - y = 0) ∧ y ≠ x := sorry
