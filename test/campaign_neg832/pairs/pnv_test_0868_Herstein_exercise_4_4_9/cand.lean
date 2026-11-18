import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

theorem dummy {p : ℕ} (hp : Nat.Prime p) : ∃ (R : Finset ℕ), R.card = Nat.div (p - 1) 2 ∧ ∀ i ∈ R, ∀ j ∈ R, ¬i ≡ j [MOD p] ∧ ∀ j : ℕ, ¬j ∈ R → ∃ (x : ℕ), x^2 ≡ j [MOD p] := sorry
