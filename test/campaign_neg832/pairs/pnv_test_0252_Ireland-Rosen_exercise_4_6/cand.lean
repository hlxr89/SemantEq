import Mathlib

open Real
open scoped BigOperators

theorem dummy [Fact p.Prime] (n : ℕ) (h : p = 2^n + 1) : Nat.Prime p ∧ 3 ≡ 1 [MOD p] ∧ ∀ (x : ℕ), x ≠ 1 → x ≠ p - 1 → ¬IsPrimitiveRoot x p := sorry
