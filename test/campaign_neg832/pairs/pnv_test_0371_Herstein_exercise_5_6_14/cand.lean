import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {F : Type*} [Field F] (hp : CharP F p) (m : ℕ) (hn : m = p ^ n) : ∀ (x : F), x ≠ 1 → x ^ m ≠ x → x ∈ roots (X - X) → true := sorry
