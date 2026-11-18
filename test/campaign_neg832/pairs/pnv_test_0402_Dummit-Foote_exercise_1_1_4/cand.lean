import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {n : ℕ} : ∀ (a b c : ℤ), (a % n) * (b % n) = (a * b) % n := sorry
