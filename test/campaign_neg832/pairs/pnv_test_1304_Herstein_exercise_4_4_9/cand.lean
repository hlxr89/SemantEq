import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {p : ℕ} (h_p : p.Prime) : ∃ (r : ℕ), r < p - 1 ∧ (∃ sq : ℕ, sq ^ 2 ≡ r [MOD p]) ∧ (∀ n : ℕ, n < p - 1 - r → ¬∃ sq : ℕ, sq ^ 2 ≡ n [MOD p]) ∧ r = (p - 1) / 2 + (p - 1) / 2 := sorry
