import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy (m n k : ℕ) : (m * n) % k * k + m * n = m * (n * k) % k * k + m * (n % k * k + n) := sorry
