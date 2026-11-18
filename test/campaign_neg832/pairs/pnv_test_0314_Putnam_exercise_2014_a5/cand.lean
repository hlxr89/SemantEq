import Mathlib

open scoped BigOperators

theorem dummy (S : Set ℕ) (hS : S.Finite) (x : ℕ) (hx : ∀ n : ℕ, n ∈ S → x ∣ n) : ∃ y : ℕ, ∀ n : ℕ, n ∈ S → y ∣ n ∧ y ∣ n - x := sorry
