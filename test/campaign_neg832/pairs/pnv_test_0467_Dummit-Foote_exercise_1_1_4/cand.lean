import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {n : ℕ} (hn : n ≠ 0) : ∀ (a b c : ℤ), (a % n) * ((b % n) * (c % n)) = ((a % n) * (b % n)) * (c % n) := sorry
