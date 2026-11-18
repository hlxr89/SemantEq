import Mathlib

open Real
open scoped BigOperators

theorem dummy {p : ℕ} : (p ≡ 1 [MOD 4] → ∃ (A B : ℤ), p = A^2 + 64*B^2) ∧ (∃ (A B : ℤ), p = A^2 + 64*B^2 → p ≡ 1 [MOD 4]) := sorry
