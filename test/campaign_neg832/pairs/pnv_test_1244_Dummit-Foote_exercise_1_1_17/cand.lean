import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy { G : Type*} [Group G] {x : G} {n : ℕ} (hn : n > 0) (hnx : x ^ n = 1) : x⁻¹ = x ^ (n - 1) := sorry
