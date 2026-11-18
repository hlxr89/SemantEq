import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy [Group G] (x : G) {n : ℕ} (hn : 1 < n) : x⁻¹ = x^(n - 1) := sorry
